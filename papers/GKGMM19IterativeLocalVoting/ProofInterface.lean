import GKGMM19IterativeLocalVoting.Assumptions
import EconCSLib.Foundations.Optimization.StochasticSubgradient
import EconCSLib.Foundations.Probability.MeasureInequalities
import Mathlib.Probability.BorelCantelli

/-!
# Proof-Facing Interface: GKGMM19 Iterative Local Voting

This file exposes compact aliases for implementation-level proof bridges that
are useful for continuing the formalization but too low-level for the
human-facing paper review surface in `PaperInterface.lean`.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace GKGMM19IterativeLocalVoting

theorem proof_probability_ae_eventually_not_of_summable_bad_events
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {bad : ℕ → α → Prop}
    (hsum : (∑' n, μ {ω | bad n ω}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ¬ bad n ω := by
  exact EconCSLib.ae_eventually_not_of_tsum_measure_setOf_ne_top
    (μ := μ) hsum

theorem proof_probability_exists_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {P : α → Prop}
    (hP : ∀ᵐ a ∂μ, P a) :
    ∃ a, P a := by
  exact hP.exists

/--
Countable a.e. intersection wrapper: if each time-indexed property holds
almost everywhere, then almost every sample path satisfies all of them.
-/
theorem proof_probability_ae_all_nat_of_forall_ae
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {P : ℕ → α → Prop}
    (hP : ∀ n : ℕ, ∀ᵐ a ∂μ, P n a) :
    ∀ᵐ a ∂μ, ∀ n : ℕ, P n a := by
  exact ae_all_iff.2 hP

/--
Finite-coordinate path bridge for Lemma 3-style bad-event avoidance: if every
time slice avoids the coordinate-equality bad event almost everywhere, then
almost every sampled ideal path has pointwise coordinate noncollision at every
time.
-/
theorem proof_coordinate_noncollision_ae_all_time_of_forall_time_ae_notMem_badEvent
    {Ω Coord : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (trajectory : ℕ → Coord → ℝ)
    (idealPath : Ω → ℕ → Coord → ℝ)
    (havoid :
      ∀ t : ℕ,
        ∀ᵐ ω ∂μ,
          idealPath ω t ∉ coordinateEqualityBadEvent (trajectory t)) :
    ∀ᵐ ω ∂μ,
      ∀ t : ℕ, ∀ i : Coord, trajectory t i ≠ idealPath ω t i := by
  have hall :
      ∀ᵐ ω ∂μ,
        ∀ t : ℕ,
          idealPath ω t ∉ coordinateEqualityBadEvent (trajectory t) :=
    proof_probability_ae_all_nat_of_forall_ae μ havoid
  filter_upwards [hall] with ω hω
  intro t
  exact
    (notMem_coordinateEqualityBadEvent_iff (trajectory t) (idealPath ω t)).mp
      (hω t)

/--
Deterministic extraction form of the preceding a.e. path bridge: on a
probability space, per-time a.e. bad-event avoidance supplies one sampled ideal
path that avoids every coordinate equality at every time.
-/
theorem proof_coordinate_noncollision_path_exists_of_forall_time_ae_notMem_badEvent
    {Ω Coord : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (trajectory : ℕ → Coord → ℝ)
    (idealPath : Ω → ℕ → Coord → ℝ)
    (havoid :
      ∀ t : ℕ,
        ∀ᵐ ω ∂μ,
          idealPath ω t ∉ coordinateEqualityBadEvent (trajectory t)) :
    ∃ ω : Ω,
      ∀ t : ℕ, ∀ i : Coord, trajectory t i ≠ idealPath ω t i := by
  exact
    proof_probability_exists_of_ae
      (proof_coordinate_noncollision_ae_all_time_of_forall_time_ae_notMem_badEvent
        μ trajectory idealPath havoid)

/--
Sampled-voter extraction form of the bad-event bridge.  If a random voter path
has per-time a.e. ideals outside the current coordinate-equality bad event,
then one deterministic voter path supplies the pointwise noncollision field
expected by the finite Model B trace record.
-/
theorem proof_coordinate_noncollision_voter_path_exists_of_forall_time_ae_notMem_badEvent
    {Ω Voter Coord : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : ILVEnvironment Voter (Coord → ℝ)) (q : ℝ)
    (voterPath : Ω → ℕ → Voter)
    (havoid :
      ∀ t : ℕ,
        ∀ᵐ ω ∂μ,
          E.ideal (voterPath ω t) ∉
            coordinateEqualityBadEvent
              (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)) :
    ∃ voter : ℕ → Voter,
      ∀ t : ℕ, ∀ i : Coord,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i ≠
          E.ideal (voter t) i := by
  rcases
      proof_coordinate_noncollision_path_exists_of_forall_time_ae_notMem_badEvent
        (μ := μ)
        (fun t =>
          E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
        (fun ω t => E.ideal (voterPath ω t)) havoid
    with ⟨ω, hω⟩
  exact ⟨voterPath ω, hω⟩

/--
Distributional form of the Lemma 3/C3 bridge for a concrete finite-coordinate
ideal distribution.  If a sampled ideal point has this bounded-density ideal
distribution as its marginal law, then the sampled ideal avoids the
coordinate-equality bad event a.e.  The measurable-set premise is kept explicit
because the ambient measurable structure on finite coordinate functions is a
source-model choice.
-/
theorem proof_coordinate_badEvent_ae_of_marginal_ideal_distribution
    {Ω Coord : Type*} [MeasurableSpace Ω] [Fintype Coord]
    {μ : Measure Ω}
    (D : FiniteCoordinateIdealDistributionData Coord)
    (idealSample : Ω → Coord → ℝ)
    (hmeas : AEMeasurable idealSample μ)
    (hlaw : Measure.map idealSample μ = D.idealMeasure)
    (x : Coord → ℝ)
    (hmeasBad : MeasurableSet (coordinateEqualityBadEvent x)) :
    ∀ᵐ ω ∂μ, idealSample ω ∉ coordinateEqualityBadEvent x := by
  have hcoord :
      ∀ᵐ ideal ∂D.idealMeasure, ∀ i, x i ≠ ideal i :=
    D.coordinate_noncollision_ae x
  have hnotBad :
      ∀ᵐ ideal ∂D.idealMeasure,
        ideal ∉ coordinateEqualityBadEvent x := by
    filter_upwards [hcoord] with ideal hideal
    exact (notMem_coordinateEqualityBadEvent_iff x ideal).2 hideal
  have hnotBadMap :
      ∀ᵐ ideal ∂Measure.map idealSample μ,
        ideal ∉ coordinateEqualityBadEvent x := by
    simpa [hlaw] using hnotBad
  exact (ae_map_iff hmeas hmeasBad.compl).1 hnotBadMap

/--
Environment-tied C3 specialization of
`proof_coordinate_badEvent_ae_of_marginal_ideal_distribution`.
-/
theorem proof_coordinate_badEvent_ae_of_marginal_ideal_law
    {Ω Voter Coord : Type*} [MeasurableSpace Ω]
    [Fintype Coord]
    {μ : Measure Ω} {E : ILVEnvironment Voter (Coord → ℝ)}
    (C : FiniteCoordinateC3Carrier E) (idealSample : Ω → Coord → ℝ)
    (hmeas : AEMeasurable idealSample μ)
    (hlaw : Measure.map idealSample μ = C.data.idealMeasure)
    (x : Coord → ℝ)
    (hmeasBad : MeasurableSet (coordinateEqualityBadEvent x)) :
    ∀ᵐ ω ∂μ, idealSample ω ∉ coordinateEqualityBadEvent x :=
  proof_coordinate_badEvent_ae_of_marginal_ideal_distribution
    C.data idealSample hmeas hlaw x hmeasBad

/--
Sampled-voter law alignment form of the coordinate noncollision bridge.  A
random selected-voter path whose ideal marginal at every time is the C3 ideal
law supplies the deterministic selected-voter noncollision field after choosing
one a.e.-good sample path.
-/
theorem proof_coordinate_noncollision_voter_path_exists_of_marginal_ideal_law
    {Ω Voter Coord : Type*} [MeasurableSpace Ω]
    [Fintype Coord]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : ILVEnvironment Voter (Coord → ℝ)) (q : ℝ)
    (C : FiniteCoordinateC3Carrier E)
    (voterPath : Ω → ℕ → Voter)
    (hmeas :
      ∀ t : ℕ,
        AEMeasurable (fun ω => E.ideal (voterPath ω t)) μ)
    (hlaw :
      ∀ t : ℕ,
        Measure.map (fun ω => E.ideal (voterPath ω t)) μ =
          C.data.idealMeasure)
    (hmeasBad :
      ∀ t : ℕ,
        MeasurableSet
          (coordinateEqualityBadEvent
            (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t))) :
    ∃ voter : ℕ → Voter,
      ∀ t : ℕ, ∀ i : Coord,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i ≠
          E.ideal (voter t) i := by
  exact
    proof_coordinate_noncollision_voter_path_exists_of_forall_time_ae_notMem_badEvent
      E q voterPath
      (fun t =>
        proof_coordinate_badEvent_ae_of_marginal_ideal_law
          (μ := μ) C (fun ω => E.ideal (voterPath ω t))
          (hmeas t) (hlaw t)
          (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
          (hmeasBad t))

/--
Sampled-process version of the finite Model B Algorithm 1 trace source.

The deterministic `FiniteModelBILVAlgorithm1PrimitiveTraceSource` stores a
single selected-voter path with all-time coordinate noncollision.  The paper's
C3 argument is probabilistic, so this source stores a probability-space voter
process whose ideal marginals are the concrete C3 ideal law, together with
raw/projection equations for every sample path.  The constructor below chooses
one a.e.-good sample path and derives the deterministic trace record.
-/
structure FiniteModelBILVAlgorithm1SampledTraceSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ)
    (C : FiniteCoordinateC3Carrier E) where
  Ω : Type
  [measurableSpace : MeasurableSpace Ω]
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  project : (Coord → ℝ) → Coord → ℝ
  voterPath : Ω → ℕ → Voter
  rawPath : Ω → ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E (SourceNorm.lp q) project
  initial_feasible :
    E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈
      E.solutionSpace
  ideal_aemeasurable :
    ∀ t : ℕ, AEMeasurable (fun ω => E.ideal (voterPath ω t)) μ
  ideal_marginal_law :
    ∀ t : ℕ,
      Measure.map (fun ω => E.ideal (voterPath ω t)) μ =
        C.data.idealMeasure
  badEvent_measurable :
    ∀ t : ℕ,
      MeasurableSet
        (coordinateEqualityBadEvent
          (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t))
  raw_update_formula :
    ∀ ω t,
      rawPath ω t =
        fun i =>
          E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
            ilvRadius r0 (t + 1) *
              lpCostGradientCandidate p
                (fun j =>
                  E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t j -
                    E.ideal (voterPath ω t) j) i
  projected_update :
    ∀ ω t,
      Algorithm1ProjectedUpdate project (rawPath ω t)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB (t + 1))

noncomputable def
    proof_finiteModelBILVAlgorithm1PrimitiveTraceSource_of_sampledTrace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    {C : FiniteCoordinateC3Carrier E}
    (S : FiniteModelBILVAlgorithm1SampledTraceSource E p q r0 C) :
    FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0 := by
  classical
  letI := S.measurableSpace
  letI := S.probability
  have havoid :
      ∀ t : ℕ,
        ∀ᵐ ω ∂S.μ,
          E.ideal (S.voterPath ω t) ∉
            coordinateEqualityBadEvent
              (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t) := by
    intro t
    exact
      proof_coordinate_badEvent_ae_of_marginal_ideal_law
        (μ := S.μ) C (fun ω => E.ideal (S.voterPath ω t))
        (S.ideal_aemeasurable t) (S.ideal_marginal_law t)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
        (S.badEvent_measurable t)
  let hgood :
      ∃ ω : S.Ω,
        ∀ t : ℕ, ∀ i : Coord,
          E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i ≠
            E.ideal (S.voterPath ω t) i :=
    proof_coordinate_noncollision_path_exists_of_forall_time_ae_notMem_badEvent
      (μ := S.μ)
      (fun t =>
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
      (fun ω t => E.ideal (S.voterPath ω t)) havoid
  let ω : S.Ω := Classical.choose hgood
  have hω :
      ∀ t : ℕ, ∀ i : Coord,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i ≠
          E.ideal (S.voterPath ω t) i :=
    Classical.choose_spec hgood
  exact
    { project := S.project
      voter := S.voterPath ω
      raw := S.rawPath ω
      project_norm := S.project_norm
      initial_feasible := S.initial_feasible
      coordinate_noncollision := hω
      raw_update_formula := S.raw_update_formula ω
      projected_update := S.projected_update ω }

/--
Concrete C3 extraction for an ideal-point sequence: a product-density C3
carrier on a probability measure supplies one ideal point avoiding a countable
trajectory in every coordinate.  This is the null-set part of the paper's
Lemma 3/C3 argument, separated from the source-specific voter-realization step.
-/
theorem proof_coordinate_noncollision_ideal_exists_of_finiteCoordinateC3Carrier
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C : FiniteCoordinateC3Carrier E)
    (hprob : IsProbabilityMeasure C.data.idealMeasure)
    (trajectory : ℕ → Coord → ℝ) :
    ∃ ideal : Coord → ℝ,
      ∀ t : ℕ, ∀ i : Coord, trajectory t i ≠ ideal i := by
  letI := hprob
  have hall :
      ∀ᵐ ideal ∂C.data.idealMeasure,
        ∀ t : ℕ, ∀ i : Coord, trajectory t i ≠ ideal i :=
    proof_probability_ae_all_nat_of_forall_ae C.data.idealMeasure
      (fun t => C.coordinate_noncollision_ae (trajectory t))
  exact proof_probability_exists_of_ae hall

/--
Finite-component a.e. path bridge: if every component of every time slice
avoids the coordinate-equality bad event a.e., then almost every sampled
component/voter path satisfies all component noncollision constraints.
-/
theorem proof_component_noncollision_ae_all_time_of_forall_time_component_ae_notMem_badEvent
    {Ω Voter Coord Component : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (components : Finset Component)
    (trajectory : ℕ → Coord → ℝ)
    (selectedVoter : Ω → ℕ → Voter)
    (componentIdeal : Component → Voter → Coord → ℝ)
    (havoid :
      ∀ t : ℕ, ∀ k : Component, k ∈ components →
        ∀ᵐ ω ∂μ,
          componentIdeal k (selectedVoter ω t) ∉
            coordinateEqualityBadEvent (trajectory t)) :
    ∀ᵐ ω ∂μ,
      ∀ t : ℕ, ∀ k : Component, k ∈ components → ∀ i : Coord,
        trajectory t i ≠ componentIdeal k (selectedVoter ω t) i := by
  have htime :
      ∀ t : ℕ,
        ∀ᵐ ω ∂μ,
          ∀ k : Component, k ∈ components →
            componentIdeal k (selectedVoter ω t) ∉
              coordinateEqualityBadEvent (trajectory t) := by
    intro t
    exact (Filter.eventually_all_finset components).2
      (fun k hk => havoid t k hk)
  have hall :
      ∀ᵐ ω ∂μ,
        ∀ t : ℕ, ∀ k : Component, k ∈ components →
          componentIdeal k (selectedVoter ω t) ∉
            coordinateEqualityBadEvent (trajectory t) :=
    proof_probability_ae_all_nat_of_forall_ae μ htime
  filter_upwards [hall] with ω hω
  intro t k hk
  exact
    (notMem_coordinateEqualityBadEvent_iff
      (trajectory t) (componentIdeal k (selectedVoter ω t))).mp
      (hω t k hk)

/--
Deterministic extraction form for the weighted-component noncollision field:
from a probability-space sampled voter path with per-component a.e. bad-event
avoidance, choose one deterministic voter path satisfying all finite component
noncollision constraints.
-/
theorem proof_component_noncollision_selected_voter_path_exists_of_forall_time_component_ae_notMem_badEvent
    {Ω Voter Coord Component : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (components : Finset Component)
    (trajectory : ℕ → Coord → ℝ)
    (selectedVoter : Ω → ℕ → Voter)
    (componentIdeal : Component → Voter → Coord → ℝ)
    (havoid :
      ∀ t : ℕ, ∀ k : Component, k ∈ components →
        ∀ᵐ ω ∂μ,
          componentIdeal k (selectedVoter ω t) ∉
            coordinateEqualityBadEvent (trajectory t)) :
    ∃ selected : ℕ → Voter,
      ∀ t : ℕ, ∀ k : Component, k ∈ components → ∀ i : Coord,
        trajectory t i ≠ componentIdeal k (selected t) i := by
  rcases
      proof_probability_exists_of_ae
        (proof_component_noncollision_ae_all_time_of_forall_time_component_ae_notMem_badEvent
          μ components trajectory selectedVoter componentIdeal havoid)
    with ⟨ω, hω⟩
  exact ⟨selectedVoter ω, hω⟩

/--
Component-wise marginal-law version of the Proposition 1 noncollision bridge.
If each sampled component ideal has a bounded-density finite-coordinate
distribution as its marginal law at every time, then one deterministic selected
voter path satisfies the component noncollision field.
-/
theorem proof_component_noncollision_selected_voter_path_exists_of_marginal_component_law
    {Ω Voter Coord Component : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype Coord]
    (components : Finset Component)
    (trajectory : ℕ → Coord → ℝ)
    (selectedVoter : Ω → ℕ → Voter)
    (componentIdeal : Component → Voter → Coord → ℝ)
    (componentDistribution :
      Component → FiniteCoordinateIdealDistributionData Coord)
    (hmeas :
      ∀ t : ℕ, ∀ k : Component, k ∈ components →
        AEMeasurable (fun ω => componentIdeal k (selectedVoter ω t)) μ)
    (hlaw :
      ∀ t : ℕ, ∀ k : Component, k ∈ components →
        Measure.map (fun ω => componentIdeal k (selectedVoter ω t)) μ =
          (componentDistribution k).idealMeasure)
    (hmeasBad :
      ∀ t : ℕ, MeasurableSet (coordinateEqualityBadEvent (trajectory t))) :
    ∃ selected : ℕ → Voter,
      ∀ t : ℕ, ∀ k : Component, k ∈ components → ∀ i : Coord,
        trajectory t i ≠ componentIdeal k (selected t) i := by
  exact
    proof_component_noncollision_selected_voter_path_exists_of_forall_time_component_ae_notMem_badEvent
      components trajectory selectedVoter componentIdeal
      (fun t k hk =>
        proof_coordinate_badEvent_ae_of_marginal_ideal_distribution
          (μ := μ) (componentDistribution k)
          (fun ω => componentIdeal k (selectedVoter ω t))
          (hmeas t k hk) (hlaw t k hk) (trajectory t) (hmeasBad t))

/--
Projected-update bookkeeping for the concrete weighted-Euclidean Proposition 1
source.  The expanded field in
`WeightedEuclideanL2ConcreteComponentTraceSource` follows from a raw Algorithm 2
generation equation plus the projection step; the remaining source-model work is
to prove those two equations from the paper's selected-voter response process.
-/
theorem proof_weightedEuclideanL2ConcreteComponent_projected_update_of_raw_generation
    {Voter Coord Component : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {selectedVoter : ℕ → Voter}
    {componentIdeal : Component → Voter → Coord → ℝ}
    {noise bias raw : ℕ → Coord → ℝ}
    (hraw :
      ∀ t : ℕ,
        raw t =
          fun i =>
            E.trajectory SourceNorm.l2 model t i -
              ilvRadius r0 (t + 1) *
                (W.components.sum
                    (fun k =>
                      (W.weight (selectedVoter t) k /
                          W.weightNorm2 (selectedVoter t)) *
                        lpCostGradientCandidate 2
                          (fun j =>
                            E.trajectory SourceNorm.l2 model t j -
                              componentIdeal k (selectedVoter t) j) i) +
                  noise t i + bias t i))
    (hproject :
      ∀ t : ℕ,
        E.trajectory SourceNorm.l2 model (t + 1) = project (raw t)) :
    ∀ t : ℕ,
      E.trajectory SourceNorm.l2 model (t + 1) =
        project
          (fun i =>
            E.trajectory SourceNorm.l2 model t i -
              ilvRadius r0 (t + 1) *
                (W.components.sum
                    (fun k =>
                      (W.weight (selectedVoter t) k /
                          W.weightNorm2 (selectedVoter t)) *
                        lpCostGradientCandidate 2
                          (fun j =>
                            E.trajectory SourceNorm.l2 model t j -
                              componentIdeal k (selectedVoter t) j) i) +
                  noise t i + bias t i)) := by
  intro t
  rw [hproject t, hraw t]

/--
Sampled-process version of the concrete weighted-Euclidean Proposition 1 trace
source.  It stores the selected-voter process, component ideal marginal laws,
and raw Algorithm 2 generation/projection equations.  The constructor below
chooses one a.e.-good sample path and derives the deterministic
`WeightedEuclideanL2ConcreteComponentTraceSource` used by the current SSGM
bridge.
-/
structure WeightedEuclideanL2ConcreteComponentSampledTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  Ω : Type
  [measurableSpace : MeasurableSpace Ω]
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoterPath : Ω → ℕ → Voter
  componentIdeal : Component → Voter → Coord → ℝ
  componentDistribution :
    Component → FiniteCoordinateIdealDistributionData Coord
  noisePath : Ω → ℕ → Coord → ℝ
  biasPath : Ω → ℕ → Coord → ℝ
  rawPath : Ω → ℕ → Coord → ℝ
  r0_pos : 0 < r0
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  coefficient_nonneg :
    ∀ ω t k, k ∈ W.components →
      0 ≤ W.weight (selectedVoterPath ω t) k /
        W.weightNorm2 (selectedVoterPath ω t)
  component_distance_eq_l2 :
    ∀ ω t k, k ∈ W.components → ∀ x : Coord → ℝ,
      W.componentDistance k x (selectedVoterPath ω t) =
        finiteCoordinateDistance SourceNorm.l2 x
          (componentIdeal k (selectedVoterPath ω t))
  component_ideal_aemeasurable :
    ∀ t k, k ∈ W.components →
      AEMeasurable
        (fun ω => componentIdeal k (selectedVoterPath ω t)) μ
  component_ideal_marginal_law :
    ∀ t k, k ∈ W.components →
      Measure.map
          (fun ω => componentIdeal k (selectedVoterPath ω t)) μ =
        (componentDistribution k).idealMeasure
  badEvent_measurable :
    ∀ t : ℕ,
      MeasurableSet
        (coordinateEqualityBadEvent
          (E.trajectory SourceNorm.l2 model t))
  raw_generation :
    ∀ ω t,
      rawPath ω t =
        fun i =>
          E.trajectory SourceNorm.l2 model t i -
            ilvRadius r0 (t + 1) *
              (W.components.sum
                  (fun k =>
                    (W.weight (selectedVoterPath ω t) k /
                        W.weightNorm2 (selectedVoterPath ω t)) *
                      lpCostGradientCandidate 2
                        (fun j =>
                          E.trajectory SourceNorm.l2 model t j -
                            componentIdeal k (selectedVoterPath ω t) j) i) +
                noisePath ω t i + biasPath ω t i)
  raw_projected_update :
    ∀ ω t,
      E.trajectory SourceNorm.l2 model (t + 1) =
        project (rawPath ω t)

noncomputable def
    proof_weightedEuclideanL2ConcreteComponentTraceSource_of_sampledTrace
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2ConcreteComponentSampledTraceSource E W model r0) :
    WeightedEuclideanL2ConcreteComponentTraceSource E W model r0 := by
  classical
  letI := S.measurableSpace
  letI := S.probability
  have havoid :
      ∀ t : ℕ, ∀ k : Component, k ∈ W.components →
        ∀ᵐ ω ∂S.μ,
          S.componentIdeal k (S.selectedVoterPath ω t) ∉
            coordinateEqualityBadEvent
              (E.trajectory SourceNorm.l2 model t) := by
    intro t k hk
    exact
      proof_coordinate_badEvent_ae_of_marginal_ideal_distribution
        (μ := S.μ) (S.componentDistribution k)
        (fun ω => S.componentIdeal k (S.selectedVoterPath ω t))
        (S.component_ideal_aemeasurable t k hk)
        (S.component_ideal_marginal_law t k hk)
        (E.trajectory SourceNorm.l2 model t)
        (S.badEvent_measurable t)
  let hgood :
      ∃ ω : S.Ω,
        ∀ t : ℕ, ∀ k : Component, k ∈ W.components → ∀ i : Coord,
          E.trajectory SourceNorm.l2 model t i ≠
            S.componentIdeal k (S.selectedVoterPath ω t) i :=
    proof_probability_exists_of_ae
      (proof_component_noncollision_ae_all_time_of_forall_time_component_ae_notMem_badEvent
        S.μ W.components
        (fun t => E.trajectory SourceNorm.l2 model t)
        S.selectedVoterPath S.componentIdeal havoid)
  let ω : S.Ω := Classical.choose hgood
  have hω :
      ∀ t : ℕ, ∀ k : Component, k ∈ W.components → ∀ i : Coord,
        E.trajectory SourceNorm.l2 model t i ≠
          S.componentIdeal k (S.selectedVoterPath ω t) i :=
    Classical.choose_spec hgood
  exact
    { project := S.project
      selectedVoter := S.selectedVoterPath ω
      componentIdeal := S.componentIdeal
      noise := S.noisePath ω
      bias := S.biasPath ω
      r0_pos := S.r0_pos
      project_norm := S.project_norm
      initial_feasible := S.initial_feasible
      coefficient_nonneg := S.coefficient_nonneg ω
      component_distance_eq_l2 := S.component_distance_eq_l2 ω
      component_noncollision := hω
      projected_update :=
        proof_weightedEuclideanL2ConcreteComponent_projected_update_of_raw_generation
          (E := E) (W := W) (model := model) (r0 := r0)
          (project := S.project)
          (selectedVoter := S.selectedVoterPath ω)
          (componentIdeal := S.componentIdeal)
          (noise := S.noisePath ω) (bias := S.biasPath ω)
          (raw := S.rawPath ω)
          (S.raw_generation ω) (S.raw_projected_update ω) }

theorem proof_probability_ae_eventually_le_of_summable_upper_bad_events
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {lhs rhs : ℕ → α → ℝ}
    (hsum : (∑' n, μ {ω | rhs n ω < lhs n ω}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n → lhs n ω ≤ rhs n ω := by
  exact EconCSLib.ae_eventually_le_of_tsum_measure_lt_ne_top
    (μ := μ) hsum

/--
Proof-facing Borel-Cantelli bridge for the Theorem 3 finite-dot fluctuation
shape: after summable upper bad events, the accumulated expected finite-dot
progress minus a fixed concentration bound is eventually below the realized
finite-dot progress plus the starting projection.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_summable_bad_events
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {expected realized : ℕ → α → ℝ} {base concentrationBound : ℝ}
    (hsum :
      (∑' n,
        μ {ω | base + realized n ω < expected n ω - concentrationBound}) ≠ ∞) :
    ∀ᵐ ω ∂μ,
      ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - concentrationBound ≤ base + realized n ω := by
  exact
    proof_probability_ae_eventually_le_of_summable_upper_bad_events
      (μ := μ)
      (lhs := fun n ω => expected n ω - concentrationBound)
      (rhs := fun n ω => base + realized n ω)
      hsum

theorem proof_probability_hasCondSubgaussianMGF_of_condKernel_bounded_centered
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hm : m ≤ mΩ)
    (h_integrable :
      ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (h_meas :
      ∀ᵐ x ∂(μ.trim hm),
        AEMeasurable X (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m x))
    (h_bound :
      ∀ᵐ x ∂(μ.trim hm),
        ∀ᵐ ω ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m x,
          X ω ∈ Set.Icc a b)
    (h_mean :
      ∀ᵐ x ∂(μ.trim hm),
        ∫ ω, X ω ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m x = 0) :
    ProbabilityTheory.HasCondSubgaussianMGF (mΩ := mΩ) m hm X
      ((‖b - a‖₊ / 2) ^ 2) μ := by
  change
    ProbabilityTheory.Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2)
      (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m) (μ.trim hm)
  exact
    @EconCSLib.kernel_hasSubgaussianMGF_of_ae_mem_Icc_of_integral_eq_zero
      Ω Ω m mΩ (μ.trim hm)
      (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m)
      inferInstance X a b
      (by
        intro t
        simpa [ProbabilityTheory.condExpKernel_comp_trim (mΩ := mΩ) (μ := μ) hm]
          using h_integrable t)
      h_meas h_bound h_mean

theorem proof_probability_azuma_hoeffding_tail_of_condSubgaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG :
      ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  exact ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    h_adapted h0 n h_subG hε

/--
Proof-facing Azuma/Borel-Cantelli adapter for the finite-dot fluctuation shape.
If the centered selected-increment process is conditionally sub-Gaussian and the
Azuma exponential tail envelope is summable at `concentrationBound`, then
almost surely the realized finite-dot progress eventually stays within that
fixed concentration bound of the expected progress.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_azuma_borelCantelli
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    {expected realized : ℕ → Ω → ℝ} {base concentrationBound : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (h_subG :
      ∀ n : ℕ, ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    (hconcentration_nonneg : 0 ≤ concentrationBound)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω)
    (hsum_bound :
      (∑' n,
        ENNReal.ofReal
          (Real.exp
            (-concentrationBound ^ 2 /
              (2 * ∑ i ∈ Finset.range n, cY i)))) ≠ ∞) :
    ∀ᵐ ω ∂μ,
      ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - concentrationBound ≤ base + realized n ω := by
  classical
  let bad : ℕ → Set Ω :=
    fun n => {ω | base + realized n ω < expected n ω - concentrationBound}
  let tailBound : ℕ → ℝ :=
    fun n =>
      Real.exp
        (-concentrationBound ^ 2 /
          (2 * ∑ i ∈ Finset.range n, cY i))
  have htail_nonneg : ∀ n : ℕ, 0 ≤ tailBound n := by
    intro n
    positivity
  have htail_real : ∀ n : ℕ, μ.real (bad n) ≤ tailBound n := by
    intro n
    have hsubset :
        bad n ⊆
          {ω | concentrationBound ≤ ∑ i ∈ Finset.range n, Y i ω} := by
      intro ω hω
      have hlt : concentrationBound < expected n ω - base - realized n ω := by
        dsimp [bad] at hω
        linarith
      have hle : concentrationBound ≤ expected n ω - base - realized n ω :=
        le_of_lt hlt
      simpa [hcentered n ω] using hle
    have hmono :
        μ.real (bad n) ≤
          μ.real {ω | concentrationBound ≤ ∑ i ∈ Finset.range n, Y i ω} :=
      measureReal_mono (μ := μ) hsubset (measure_ne_top μ _)
    have hazuma :
        μ.real {ω | concentrationBound ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
          tailBound n := by
      simpa [tailBound] using
        proof_probability_azuma_hoeffding_tail_of_condSubgaussian
          (μ := μ) (Y := Y) (cY := cY) (ℱ := ℱ)
          h_adapted h0 n (h_subG n) hconcentration_nonneg
    exact hmono.trans hazuma
  have hsum_bad : (∑' n, μ (bad n)) ≠ ∞ := by
    exact
      EconCSLib.tsum_measure_ne_top_of_measureReal_le_of_tsum_ofReal_ne_top
        (μ := μ) (bad := bad) (bound := tailBound)
        htail_nonneg htail_real
        (by simpa [tailBound] using hsum_bound)
  simpa [bad] using
    proof_theorem3_finiteDot_eventual_fluctuation_of_summable_bad_events
      (μ := μ) (expected := expected) (realized := realized)
      (base := base) (concentrationBound := concentrationBound) hsum_bad

/--
If the centered finite-dot partial sums are eventually bounded above almost
surely, rewriting the centered identity gives the finite-dot fluctuation control
used by the deterministic Theorem 3 chain.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_ae_eventually_partial_sum_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hupper :
      ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ i ∈ Finset.range n, Y i ω) ≤ upper)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  filter_upwards [hupper] with ω hω
  rcases hω with ⟨upper, T, hT⟩
  refine ⟨upper, T, ?_⟩
  intro n hn
  have hle :
      expected n ω - base - realized n ω ≤ upper := by
    simpa [← hcentered n ω] using hT n hn
  linarith

/--
If the centered finite-dot partial sums converge almost surely, then their
paths are eventually bounded above.  Rewriting the centered identity gives the
finite-dot fluctuation control used by the deterministic Theorem 3 chain.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_ae_partial_sum_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hconv :
      ∀ᵐ ω ∂μ, ∃ limit : ℝ,
        Filter.Tendsto
          (fun n : ℕ => ∑ i ∈ Finset.range n, Y i ω)
          Filter.atTop (nhds limit))
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hupper :
      ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ i ∈ Finset.range n, Y i ω) ≤ upper := by
    exact
      EconCSLib.ae_eventually_le_of_ae_exists_tendsto
        (μ := μ)
        (S := fun n ω => ∑ i ∈ Finset.range n, Y i ω)
        hconv
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_ae_eventually_partial_sum_le
      (μ := μ) (Y := Y) (expected := expected) (realized := realized)
      (base := base) hupper hcentered

/--
Martingale-convergence route for Theorem 3 finite-dot fluctuation control.
This is the probability-theory replacement for the prefix-Azuma summability
adapter in the square-summable-radius regime: an L1-bounded centered partial
sum martingale converges almost surely, hence is eventually bounded above.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_martingale_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_martingale :
      MeasureTheory.Martingale
        (fun n ω => ∑ i ∈ Finset.range n, Y i ω) ℱ μ)
    (h_L1 :
      ∀ n : ℕ,
        MeasureTheory.eLpNorm
          (fun ω => ∑ i ∈ Finset.range n, Y i ω) 1 μ ≤ R)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hconv :
      ∀ᵐ ω ∂μ, ∃ limit : ℝ,
        Filter.Tendsto
          (fun n : ℕ => ∑ i ∈ Finset.range n, Y i ω)
          Filter.atTop (nhds limit) := by
    exact
      MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd
        h_martingale.submartingale h_L1
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_ae_partial_sum_tendsto
      (μ := μ) (Y := Y) (expected := expected) (realized := realized)
      (base := base) hconv hcentered

/--
`L2`-bounded martingale route for Theorem 3 finite-dot fluctuation control.
This is the natural square-summable-radius handoff: once the centered partial
sum martingale has a uniform `L2` bound, probability-space monotonicity gives
the `L1` bound required by Mathlib's martingale convergence theorem.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_martingale_L2_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_martingale :
      MeasureTheory.Martingale
        (fun n ω => ∑ i ∈ Finset.range n, Y i ω) ℱ μ)
    (h_L2 :
      ∀ n : ℕ,
        MeasureTheory.eLpNorm
          (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ ≤ R)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hupper :
      ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ i ∈ Finset.range n, Y i ω) ≤ upper := by
    exact
      EconCSLib.ae_eventually_le_of_martingale_L2_bdd
        (S := fun n ω => ∑ i ∈ Finset.range n, Y i ω)
        (ℱ := ℱ) (R := R) h_martingale h_L2
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_ae_eventually_partial_sum_le
      (μ := μ) (Y := Y) (expected := expected) (realized := realized)
      (base := base) hupper hcentered

/--
Conditional-mean-zero route for Theorem 3 finite-dot fluctuation control.  This
packages the concrete stochastic obligation in one-step terms: the centered
selected-voter increments are adapted/integrable, have zero conditional
expectation given the current history, and their partial sums are L1-bounded.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (h_L1 :
      ∀ n : ℕ,
        MeasureTheory.eLpNorm
          (fun ω => ∑ i ∈ Finset.range n, Y i ω) 1 μ ≤ R)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hmartingale :
      MeasureTheory.Martingale
        (fun n ω => ∑ i ∈ Finset.range n, Y i ω) ℱ μ := by
    exact
      EconCSLib.martingale_partial_sum_of_condExp_eq_zero
        (Y := Y) (ℱ := ℱ) hadapted hintegrable hcond_zero
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_martingale_L1_bdd
      (μ := μ) (Y := Y) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hmartingale h_L1 hcentered

/--
Conditional-mean-zero plus `L2`-bounded partial-sum route for Theorem 3
finite-dot fluctuation control.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_L2_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (h_L2 :
      ∀ n : ℕ,
        MeasureTheory.eLpNorm
          (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ ≤ R)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hmartingale :
      MeasureTheory.Martingale
        (fun n ω => ∑ i ∈ Finset.range n, Y i ω) ℱ μ := by
    exact
      EconCSLib.martingale_partial_sum_of_condExp_eq_zero
        (Y := Y) (ℱ := ℱ) hadapted hintegrable hcond_zero
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_martingale_L2_bdd
      (μ := μ) (Y := Y) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hmartingale h_L2 hcentered

/--
Second-moment route for Theorem 3 finite-dot fluctuation control.  This is a
more concrete form of the `L2` route: callers provide square integrability and
a uniform bound on real second moments of the centered partial sums, and the
probability library converts that to the `eLpNorm` bound.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_secondMoment_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hsecond :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤ (R : ℝ) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hupper :
      ∀ᵐ ω ∂μ, ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ i ∈ Finset.range n, Y i ω) ≤ upper := by
    exact
      EconCSLib.ae_eventually_le_of_partial_sum_condExp_zero_secondMoment_bdd
        (Y := Y) (ℱ := ℱ) (R := R)
        hadapted hintegrable hmemL2 hcond_zero hsecond
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_ae_eventually_partial_sum_le
      (μ := μ) (Y := Y) (expected := expected) (realized := realized)
      (base := base) hupper hcentered

/--
Cross-moment route for the real second-moment estimate needed by Theorem 3.
This exposes the standard martingale-difference calculation: per-increment
second moments accumulate, and the partial-sum cross moment with the next
increment is nonpositive.
-/
theorem proof_probability_partial_sum_secondMoment_le_of_cross_nonpos
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ} {R : ℝ≥0}
    (hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ)
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ b n)
    (hcross_nonpos :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0)
    (hbound : ∀ n : ℕ, (∑ i ∈ Finset.range n, b i) ≤ (R : ℝ) ^ 2) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤ (R : ℝ) ^ 2 := by
  exact
    EconCSLib.partial_sum_secondMoment_le_of_cross_nonpos
      (Y := Y) (b := b) (R := R)
      (fun n => (hmemL2 n).integrable_sq)
      hcross_int hY_sq_int hY_second hcross_nonpos hbound

/--
Theorem 3 finite-dot fluctuation from conditional mean zero plus the explicit
cross-moment/second-moment estimates for the centered increments.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_crossMoment_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ b n)
    (hcross_nonpos :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0)
    (hbound : ∀ n : ℕ, (∑ i ∈ Finset.range n, b i) ≤ (R : ℝ) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hsecond :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤ (R : ℝ) ^ 2 := by
    exact
      proof_probability_partial_sum_secondMoment_le_of_cross_nonpos
        (Y := Y) (b := b) (R := R)
        hmemL2 hcross_int hY_sq_int hY_second hcross_nonpos hbound
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_secondMoment_bdd
      (μ := μ) (Y := Y) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted hintegrable hmemL2 hcond_zero hsecond hcentered

/--
Cross-moment nonpositivity derived from conditional mean-zero and adaptedness.
-/
theorem proof_probability_partial_sum_cross_integral_nonpos_of_condExp_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_integrable : ∀ n : ℕ, Integrable (Y n) μ)
    (hcond_zero : ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0) :
    ∀ n : ℕ,
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0 := by
  exact
    EconCSLib.partial_sum_cross_integral_nonpos_of_condExp_eq_zero
      (Y := Y) (ℱ := ℱ) hadapted hcross_int hY_integrable hcond_zero

/--
Theorem 3 finite-dot fluctuation from conditional mean zero, explicit
per-increment second-moment bounds, and a summable bound sequence.  The
cross-term estimate is proved from conditional mean-zero and adaptedness.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_incrementSecondMoment_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ)
    (hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ)
    (hY_integrable : ∀ n : ℕ, Integrable (Y n) μ)
    (hY_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ b n)
    (hbound : ∀ n : ℕ, (∑ i ∈ Finset.range n, b i) ≤ (R : ℝ) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hcross_nonpos :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂μ) ≤ 0 := by
    exact
      proof_probability_partial_sum_cross_integral_nonpos_of_condExp_zero
        (Y := Y) (ℱ := ℱ) hadapted hcross_int hY_integrable hcond_zero
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_crossMoment_bdd
      (μ := μ) (Y := Y) (b := b) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted hintegrable hmemL2 hcond_zero hcross_int hY_sq_int
      hY_second hcross_nonpos hbound hcentered

/--
Bounded centered increments imply the per-increment second-moment bounds used
by the martingale-difference route.  This is the probabilistic shape needed for
Theorem 3 after the concrete selected-voter increment bounds are established.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ)
    (hc : ∀ n : ℕ, 0 ≤ c n)
    (hY_abs_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n)
    (hbound :
      ∀ n : ℕ, (∑ i ∈ Finset.range n, (c i) ^ 2) ≤ (R : ℝ) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hadapted :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω) := by
    exact EconCSLib.stronglyAdapted_partial_sum_of_stronglyAdapted h_adapted
  have hY_integrable : ∀ n : ℕ, Integrable (Y n) μ := by
    intro n
    refine Integrable.of_bound (C := c n) (hY_aemeas n) ?_
    simpa [Real.norm_eq_abs] using hY_abs_bound n
  have hY_memL2 : ∀ n : ℕ, MemLp (Y n) 2 μ := by
    intro n
    exact MemLp.of_bound (μ := μ) (p := 2) (hY_aemeas n) (c n)
      (by simpa [Real.norm_eq_abs] using hY_abs_bound n)
  have hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ := by
    intro n
    exact MeasureTheory.integrable_finset_sum (Finset.range n)
      (fun i _hi => hY_integrable i)
  have hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ := by
    intro n
    exact MeasureTheory.memLp_finset_sum (Finset.range n)
      (fun i _hi => hY_memL2 i)
  have hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ := by
    intro n
    exact MemLp.integrable_mul (p := 2) (q := 2)
      (hmemL2 n) (hY_memL2 n)
  have hY_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ := by
    exact
      EconCSLib.integrable_sq_of_ae_abs_le_sequence
        (μ := μ) (Y := Y) (c := c) hY_aemeas hc hY_abs_bound
  have hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ (c n) ^ 2 := by
    exact
      EconCSLib.integral_sq_le_sq_of_ae_abs_le_sequence
        (μ := μ) (Y := Y) (c := c) hY_sq_int hc hY_abs_bound
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_incrementSecondMoment_bdd
      (μ := μ) (Y := Y) (b := fun i => (c i) ^ 2) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted hintegrable hmemL2 hcond_zero hcross_int hY_integrable
      hY_sq_int hY_second hbound hcentered

/--
Bounded centered increments imply Theorem 3 finite-dot fluctuation when the
partial sums, rather than the future increments themselves, are adapted to the
filtration.  This is the right shape for martingale differences whose
one-step voter draw is independent of the past.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_bdd_partialSumAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted_sum :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ)
    (hc : ∀ n : ℕ, 0 ≤ c n)
    (hY_abs_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n)
    (hbound :
      ∀ n : ℕ, (∑ i ∈ Finset.range n, (c i) ^ 2) ≤ (R : ℝ) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hY_integrable : ∀ n : ℕ, Integrable (Y n) μ := by
    intro n
    refine Integrable.of_bound (C := c n) (hY_aemeas n) ?_
    simpa [Real.norm_eq_abs] using hY_abs_bound n
  have hY_memL2 : ∀ n : ℕ, MemLp (Y n) 2 μ := by
    intro n
    exact MemLp.of_bound (μ := μ) (p := 2) (hY_aemeas n) (c n)
      (by simpa [Real.norm_eq_abs] using hY_abs_bound n)
  have hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ := by
    intro n
    exact MeasureTheory.integrable_finset_sum (Finset.range n)
      (fun i _hi => hY_integrable i)
  have hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ := by
    intro n
    exact MeasureTheory.memLp_finset_sum (Finset.range n)
      (fun i _hi => hY_memL2 i)
  have hcross_int :
      ∀ n : ℕ,
        Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) μ := by
    intro n
    exact MemLp.integrable_mul (p := 2) (q := 2)
      (hmemL2 n) (hY_memL2 n)
  have hY_sq_int :
      ∀ n : ℕ, Integrable (fun ω => (Y n ω) ^ 2) μ := by
    exact
      EconCSLib.integrable_sq_of_ae_abs_le_sequence
        (μ := μ) (Y := Y) (c := c) hY_aemeas hc hY_abs_bound
  have hY_second :
      ∀ n : ℕ, (∫ ω, (Y n ω) ^ 2 ∂μ) ≤ (c n) ^ 2 := by
    exact
      EconCSLib.integral_sq_le_sq_of_ae_abs_le_sequence
        (μ := μ) (Y := Y) (c := c) hY_sq_int hc hY_abs_bound
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_incrementSecondMoment_bdd
      (μ := μ) (Y := Y) (b := fun i => (c i) ^ 2) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hintegrable hmemL2 hcond_zero hcross_int hY_integrable
      hY_sq_int hY_second hbound hcentered

/--
Square-summable bounded centered increments imply the finite-dot fluctuation
control needed by Theorem 3.  The uniform second-moment bound is constructed
internally from the summable sequence of squared increment bounds.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_summable
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ)
    (hc : ∀ n : ℕ, 0 ≤ c n)
    (hY_abs_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n)
    (hsummable_sq : Summable fun n : ℕ => (c n) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  rcases EconCSLib.exists_nnreal_sq_bound_of_summable_nonneg
      (b := fun n : ℕ => (c n) ^ 2)
      hsummable_sq (fun n => sq_nonneg (c n)) with
    ⟨R, hbound⟩
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_bdd
      (μ := μ) (Y := Y) (c := c) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      h_adapted hcond_zero hY_aemeas hc hY_abs_bound hbound hcentered

/--
Square-summable bounded centered increments imply Theorem 3 finite-dot
fluctuation from a past-adapted partial-sum process.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_summable_partialSumAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted_sum :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ)
    (hc : ∀ n : ℕ, 0 ≤ c n)
    (hY_abs_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n)
    (hsummable_sq : Summable fun n : ℕ => (c n) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  rcases EconCSLib.exists_nnreal_sq_bound_of_summable_nonneg
      (b := fun n : ℕ => (c n) ^ 2)
      hsummable_sq (fun n => sq_nonneg (c n)) with
    ⟨R, hbound⟩
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_bdd_partialSumAdapted
      (μ := μ) (Y := Y) (c := c) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hcond_zero hY_aemeas hc hY_abs_bound hbound hcentered

/-- Partial sums of adapted selected increments are adapted. -/
theorem proof_probability_partial_sum_stronglyAdapted_of_stronglyAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ Y) :
    StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω) := by
  exact EconCSLib.stronglyAdapted_partial_sum_of_stronglyAdapted h_adapted

/--
If `X` is strongly measurable, the shifted partial sums
`∑_{i<n} X (i+1)` are adapted to the natural filtration of `X`.  This models
the martingale-difference convention where time `n` conditions on the first
`n` draws and the next increment is `X (n+1)`.
-/
theorem proof_probability_shifted_partial_sum_stronglyAdapted_natural
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ}
    (hX_sm : ∀ n : ℕ, StronglyMeasurable (X n)) :
    StronglyAdapted (Filtration.natural X hX_sm)
      (fun n ω => ∑ i ∈ Finset.range n, X (i + 1) ω) := by
  intro n
  have hX_adapted :
      StronglyAdapted (Filtration.natural X hX_sm) X :=
    Filtration.stronglyAdapted_natural hX_sm
  have hsum :
      StronglyMeasurable[(Filtration.natural X hX_sm) n]
        (∑ i ∈ Finset.range n, X (i + 1)) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun i hi =>
      (hX_adapted (i + 1)).mono
        ((Filtration.natural X hX_sm).mono
          (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
  convert hsum using 1
  ext ω
  simp

theorem proof_probability_iIndepFun_condExp_succ_natural_ae_eq_mean
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX_sm : ∀ n : ℕ, StronglyMeasurable (X n))
    (hX_indep : ProbabilityTheory.iIndepFun X μ) :
    ∀ n : ℕ,
      μ[X (n + 1) | Filtration.natural X hX_sm n] =ᵐ[μ]
        fun _ => ∫ ω, X (n + 1) ω ∂μ := by
  intro n
  simpa using
    ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt
      hX_sm hX_indep (Nat.lt_succ_self n)

theorem proof_probability_iIndepFun_condExp_succ_natural_ae_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX_sm : ∀ n : ℕ, StronglyMeasurable (X n))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hmean_zero : ∀ n : ℕ, (∫ ω, X (n + 1) ω ∂μ) = 0) :
    ∀ n : ℕ,
      μ[X (n + 1) | Filtration.natural X hX_sm n] =ᵐ[μ] 0 := by
  intro n
  exact
    (proof_probability_iIndepFun_condExp_succ_natural_ae_eq_mean
      (μ := μ) hX_sm hX_indep n).trans
      (Filter.Eventually.of_forall fun ω => by simp [hmean_zero n])

/--
Conditional sub-Gaussian selected increments give integrability of every
finite centered partial sum.
-/
theorem proof_probability_partial_sum_integrable_of_condSubgaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG :
      ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ) :
    Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ := by
  exact
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      h_adapted h0 n h_subG).integrable

/--
Conditional sub-Gaussian selected increments give `L2` membership of every
finite centered partial sum.
-/
theorem proof_probability_partial_sum_memLp_two_of_condSubgaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG :
      ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ := by
  exact
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      h_adapted h0 n h_subG).memLp 2

/--
Theorem 3 finite-dot fluctuation from the concrete stochastic ingredients
available after bounded-centered selected-voter increments are established:
adapted conditional sub-Gaussian increments, one-step conditional mean zero,
and a uniform L1 bound on centered partial sums.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condSubgaussian_condExp_zero_L1_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (h_subG :
      ∀ n : ℕ, ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (h_L1 :
      ∀ n : ℕ,
        MeasureTheory.eLpNorm
          (fun ω => ∑ i ∈ Finset.range n, Y i ω) 1 μ ≤ R)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hadapted_sum :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω) := by
    exact proof_probability_partial_sum_stronglyAdapted_of_stronglyAdapted
      (Y := Y) (ℱ := ℱ) h_adapted
  have hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ := by
    intro n
    exact
      proof_probability_partial_sum_integrable_of_condSubgaussian
        (μ := μ) (Y := Y) (cY := cY) (ℱ := ℱ)
        h_adapted h0 n (h_subG n)
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_L1_bdd
      (μ := μ) (Y := Y) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hintegrable hcond_zero h_L1 hcentered

/--
Theorem 3 finite-dot fluctuation from adapted conditional sub-Gaussian
increments, one-step conditional mean zero, and a uniform `L2` bound on centered
partial sums.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condSubgaussian_condExp_zero_L2_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (h_subG :
      ∀ n : ℕ, ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (h_L2 :
      ∀ n : ℕ,
        MeasureTheory.eLpNorm
          (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ ≤ R)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hadapted_sum :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω) := by
    exact proof_probability_partial_sum_stronglyAdapted_of_stronglyAdapted
      (Y := Y) (ℱ := ℱ) h_adapted
  have hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ := by
    intro n
    exact
      proof_probability_partial_sum_integrable_of_condSubgaussian
        (μ := μ) (Y := Y) (cY := cY) (ℱ := ℱ)
        h_adapted h0 n (h_subG n)
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_L2_bdd
      (μ := μ) (Y := Y) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hintegrable hcond_zero h_L2 hcentered

/--
Theorem 3 finite-dot fluctuation from adapted conditional sub-Gaussian
increments, one-step conditional mean zero, and a uniform real second-moment
bound on centered partial sums.  The conditional sub-Gaussian hypotheses
discharge integrability and `L2` membership; the only remaining numeric
probability estimate is the explicit second-moment bound.
-/
theorem proof_theorem3_finiteDot_eventual_fluctuation_of_condSubgaussian_condExp_zero_secondMoment_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    {ℱ : Filtration (Ω := Ω) ℕ mΩ} {R : ℝ≥0}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) μ)
    (h_subG :
      ∀ n : ℕ, ∀ i < n - 1,
        ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hsecond :
      ∀ n : ℕ,
        (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂μ) ≤ (R : ℝ) ^ 2)
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  have hadapted_sum :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω) := by
    exact proof_probability_partial_sum_stronglyAdapted_of_stronglyAdapted
      (Y := Y) (ℱ := ℱ) h_adapted
  have hintegrable :
      ∀ n : ℕ,
        Integrable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ := by
    intro n
    exact
      proof_probability_partial_sum_integrable_of_condSubgaussian
        (μ := μ) (Y := Y) (cY := cY) (ℱ := ℱ)
        h_adapted h0 n (h_subG n)
  have hmemL2 :
      ∀ n : ℕ,
        MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 μ := by
    intro n
    exact
      proof_probability_partial_sum_memLp_two_of_condSubgaussian
        (μ := μ) (Y := Y) (cY := cY) (ℱ := ℱ)
        h_adapted h0 n (h_subG n)
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_secondMoment_bdd
      (μ := μ) (Y := Y) (ℱ := ℱ) (R := R)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hintegrable hmemL2 hcond_zero hsecond hcentered

theorem proof_theorem1NormPair_l2_l2 :
    Theorem1NormPair SourceNorm.l2 SourceNorm.l2 := by
  exact theorem1NormPair_l2_l2

theorem proof_theorem1NormPair_l1_linf :
    Theorem1NormPair SourceNorm.l1 SourceNorm.linfty := by
  exact theorem1NormPair_l1_linf

theorem proof_theorem1NormPair_linf_l1 :
    Theorem1NormPair SourceNorm.linfty SourceNorm.l1 := by
  exact theorem1NormPair_linf_l1

theorem proof_holderDualFinite_symm {p q : ℝ}
    (h : HolderDualFinite p q) :
    HolderDualFinite q p := by
  exact HolderDualFinite.symm h

theorem proof_holderDualFinite_two_two :
    HolderDualFinite 2 2 := by
  exact HolderDualFinite.two_two

/--
Meta-level counterexample for the current abstract environment interface:
the `solutionSpace_nonempty_bounded_closed_convex` field is a bare proposition,
so `ConditionsC123` alone does not logically imply actual Lean convexity of the
solution-space set.  The paper-facing route therefore needs an explicit
`C1ConvexSolutionSpaceSource` or a stronger source model, not just
`ConditionsC123`.
-/
def nonconvexConditionsCounterexampleEnvironment : ILVEnvironment Unit ℝ where
  solutionSpace := {x | x = 0 ∨ x = 1}
  utility := fun _ _ => 0
  ideal := fun _ => 0
  normDistance := fun _ _ _ => 0
  trajectory := fun _ _ _ => 0
  societalUtility := fun _ => 0
  socialOptimal := {0}
  medianSet := {0}
  directionalField := fun _ => 0
  zeroDirection := 0
  utilityGradient := fun _ _ => 0
  scalarDirection := fun a x => a * x
  voterExpectation := fun f => f ()
  convergesWithProbabilityOne := fun _ _ => True
  convergesToPoint := fun _ _ => True
  respondsAccordingTo := fun _ => True
  solutionSpace_nonempty_bounded_closed_convex := True
  uniqueIdealSolutions := True
  idealDistribution_bounded_measurable_density := True
  directionalFieldUniformlyContinuous := True

theorem proof_conditionsC123_not_force_convex_solutionSpace :
    ∃ E : ILVEnvironment Unit ℝ,
      ConditionsC123 E ∧ ¬ Convex ℝ E.solutionSpace := by
  refine
    ⟨nonconvexConditionsCounterexampleEnvironment, ?_, ?_⟩
  · exact ⟨trivial, trivial, trivial⟩
  · intro hconv
    have h0 :
        (0 : ℝ) ∈
          nonconvexConditionsCounterexampleEnvironment.solutionSpace := by
      simp [nonconvexConditionsCounterexampleEnvironment]
    have h1 :
        (1 : ℝ) ∈
          nonconvexConditionsCounterexampleEnvironment.solutionSpace := by
      simp [nonconvexConditionsCounterexampleEnvironment]
    have hmid :=
      (convex_iff_add_mem.mp hconv) h0 h1
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
    norm_num [nonconvexConditionsCounterexampleEnvironment] at hmid

/--
Meta-level counterexample for the pathwise noncollision fields in the finite
Model B trace source.  The abstract C3 flag can hold while the realized
trajectory and the selected ideal collide in every coordinate, so the
pointwise `coordinate_noncollision` premise must be constructed from a stronger
sample-path model or kept as explicit proof debt.
-/
def pathwiseNoncollisionCounterexampleEnvironment :
    ILVEnvironment Unit (Unit → ℝ) where
  solutionSpace := Set.univ
  utility := fun _ _ => 0
  ideal := fun _ _ => 0
  normDistance := fun _ _ _ => 0
  trajectory := fun _ _ _ _ => 0
  societalUtility := fun _ => 0
  socialOptimal := Set.univ
  medianSet := Set.univ
  directionalField := fun _ _ => 0
  zeroDirection := fun _ => 0
  utilityGradient := fun _ _ _ => 0
  scalarDirection := fun a x i => a * x i
  voterExpectation := fun f => f ()
  convergesWithProbabilityOne := fun _ _ => True
  convergesToPoint := fun _ _ => True
  respondsAccordingTo := fun _ => True
  solutionSpace_nonempty_bounded_closed_convex := True
  uniqueIdealSolutions := True
  idealDistribution_bounded_measurable_density := True
  directionalFieldUniformlyContinuous := True

theorem proof_conditionsC123_not_force_pathwise_coordinate_noncollision :
    ConditionsC123 pathwiseNoncollisionCounterexampleEnvironment ∧
      ¬ (∀ voter : ℕ → Unit, ∀ t : ℕ, ∀ i : Unit,
        pathwiseNoncollisionCounterexampleEnvironment.trajectory
            (SourceNorm.lp 2) VoterResponseModel.modelB t i ≠
          pathwiseNoncollisionCounterexampleEnvironment.ideal (voter t) i) := by
  refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
  intro hnoncollision
  have hbad := hnoncollision (fun _ => ()) 0 ()
  simpa [pathwiseNoncollisionCounterexampleEnvironment] using hbad

theorem proof_pathwise_collision_counterexample_no_finiteModelB_trace_source
    (p q r0 : ℝ) :
    ¬ Nonempty
      (FiniteModelBILVAlgorithm1PrimitiveTraceSource
        pathwiseNoncollisionCounterexampleEnvironment p q r0) := by
  rintro ⟨S⟩
  have hbad := S.coordinate_noncollision 0 ()
  simpa [pathwiseNoncollisionCounterexampleEnvironment] using hbad

/--
The same issue appears in the weighted-Euclidean component route: the abstract
C1-C3 flags alone do not rule out a component ideal that collides with the
current iterate.  The full Proposition 1 component record therefore needs a
sample-path/bad-event bridge, not just the abstract C3 proposition.
-/
theorem proof_conditionsC123_not_force_pathwise_component_noncollision :
    ConditionsC123 pathwiseNoncollisionCounterexampleEnvironment ∧
      ¬ (∀ (componentIdeal : Unit → Unit → Unit → ℝ)
            (selectedVoter : ℕ → Unit),
          ∀ t : ℕ, ∀ k : Unit, ∀ i : Unit,
            pathwiseNoncollisionCounterexampleEnvironment.trajectory
                SourceNorm.l2 VoterResponseModel.modelB t i ≠
              componentIdeal k (selectedVoter t) i) := by
  refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
  intro hnoncollision
  have hbad :=
    hnoncollision (fun _ _ _ => (0 : ℝ)) (fun _ => ()) 0 () ()
  simpa [pathwiseNoncollisionCounterexampleEnvironment] using hbad

/--
Meta-level counterexample for Theorem 3's current abstract environment
interface.  Convexity, projection-compatible constant trajectories,
convergence, uniform continuity, and the displayed directional-field formula do
not by themselves imply the directional-equilibrium conclusion.  The missing
ingredient is exactly the projected feasible-step geometry now isolated in
`FiniteTheorem3GlobalProjectedLimitGradientFeasibilitySource`.
-/
def theorem3AbstractProjectionCounterexampleEnvironment :
    ILVEnvironment Unit ℝ where
  solutionSpace := {x | x = 0}
  utility := fun _ _ => 0
  ideal := fun _ => 0
  normDistance := fun _ x y => |x - y|
  trajectory := fun _ _ _ => 0
  societalUtility := fun _ => 0
  socialOptimal := {0}
  medianSet := {0}
  directionalField := fun _ => 1
  zeroDirection := 0
  utilityGradient := fun _ _ => 1
  scalarDirection := fun a x => a * x
  voterExpectation := fun f => f ()
  convergesWithProbabilityOne := fun _ _ => True
  convergesToPoint := fun _ _ => True
  respondsAccordingTo := fun _ => True
  solutionSpace_nonempty_bounded_closed_convex := True
  uniqueIdealSolutions := True
  idealDistribution_bounded_measurable_density := True
  directionalFieldUniformlyContinuous := True

theorem proof_theorem3_abstract_hypotheses_do_not_imply_statement :
    ¬ theorem3Statement theorem3AbstractProjectionCounterexampleEnvironment := by
  intro hTheorem3
  have hG :
      Theorem3DirectionalFieldFormula
        theorem3AbstractProjectionCounterexampleEnvironment := by
    intro x
    norm_num [Theorem3DirectionalFieldFormula,
      theorem3AbstractProjectionCounterexampleEnvironment]
  have hC :
      ConditionsC123 theorem3AbstractProjectionCounterexampleEnvironment := by
    exact ⟨trivial, trivial, trivial⟩
  have hConclusion :
      IsDirectionalEquilibrium
        theorem3AbstractProjectionCounterexampleEnvironment 0 :=
    hTheorem3 hG hC trivial trivial 0 trivial
  norm_num [IsDirectionalEquilibrium,
    theorem3AbstractProjectionCounterexampleEnvironment] at hConclusion

/--
The aggregate projected-feasibility source now used by the Theorem 3 route is
not a consequence of convexity alone: in a singleton feasible set, no positive
step along a nonzero direction can remain feasible.
-/
theorem proof_singleton_solutionSpace_feasible_direction_eq_zero
    {Coord : Type*} [Fintype Coord]
    {point direction : Coord → ℝ}
    (hfeasible :
      FiniteFeasibleDirectionAt ({x : Coord → ℝ | x = point})
        point direction) :
    direction = fun _ => (0 : ℝ) := by
  rcases hfeasible with ⟨η, hηpos, hmem⟩
  funext i
  have hcoord :
      point i + η * direction i = point i := by
    exact congrArg (fun x : Coord → ℝ => x i) hmem
  nlinarith

theorem proof_singleton_solutionSpace_not_force_aggregate_feasible_direction :
    ¬ FiniteFeasibleDirectionAt
      ({x : Unit → ℝ | x () = 0})
      (fun _ : Unit => (0 : ℝ))
      (fun _ : Unit => (1 : ℝ)) := by
  rintro ⟨η, hηpos, hmem⟩
  have hzero : η = 0 := by
    simpa using hmem
  linarith

theorem proof_theorem1Statement_l2_l2_modelA
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l2)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelA := by
  exact theorem1Statement_l2_l2_modelA h hC hUtil hResponse

theorem proof_theorem1Statement_l2_l2_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l2)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelB := by
  exact theorem1Statement_l2_l2_modelB h hC hUtil hResponse

theorem proof_theorem1Statement_l1_linf_modelA
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.linfty VoterResponseModel.modelA := by
  exact theorem1Statement_l1_linf_modelA h hC hUtil hResponse

theorem proof_theorem1Statement_l1_linf_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.linfty VoterResponseModel.modelB := by
  exact theorem1Statement_l1_linf_modelB h hC hUtil hResponse

theorem proof_theorem1Statement_linf_l1_modelA
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.l1 VoterResponseModel.modelA := by
  exact theorem1Statement_linf_l1_modelA h hC hUtil hResponse

theorem proof_theorem1Statement_linf_l1_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.l1 VoterResponseModel.modelB := by
  exact theorem1Statement_linf_l1_modelB h hC hUtil hResponse

theorem proof_theorem1Statement_of_sourceBridge_ssgmConvergence
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hSource : Theorem1SourceToSSGMBridge E)
    (hSSGM : Theorem1SSGMConvergenceTheorem E) :
    theorem1Statement E := by
  exact theorem1Statement_of_sourceBridge_ssgmConvergence hSource hSSGM

def proof_theorem1SourceToSSGMBridge_of_visible_hypotheses
    {Voter Point : Type*} (E : ILVEnvironment Voter Point) :
    Theorem1SourceToSSGMBridge E where
  case_certificate hC hUtil hmodel hResponse hpq :=
    { conditions := hC
      utilities := hUtil
      model_choice := hmodel
      response := hResponse
      norm_pair := hpq }

theorem proof_theorem1_caseCertificate_of_visible_hypotheses
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    {p q : SourceNorm} {model : VoterResponseModel}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E p)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model)
    (hpq : Theorem1NormPair p q) :
    Theorem1SSGMCaseCertificate E p q model := by
  exact
    (proof_theorem1SourceToSSGMBridge_of_visible_hypotheses E).case_certificate
      hC hUtil hmodel hResponse hpq

theorem proof_theorem1Statement_of_sourceBridge_ssgmBoundary
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hSource : Theorem1SourceToSSGMBridge E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Theorem1SSGMConvergenceTheorem E)) :
    theorem1Statement E := by
  exact theorem1Statement_of_sourceBridge_ssgmConvergence hSource
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_theorem1Statement_of_ssgmBoundary
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Theorem1SSGMConvergenceTheorem E)) :
    theorem1Statement E := by
  exact proof_theorem1Statement_of_sourceBridge_ssgmBoundary
    (proof_theorem1SourceToSSGMBridge_of_visible_hypotheses E) hBoundary

theorem proof_theorem2Statement_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem2Statement E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    ILVConvergesToSocietalOptimal E (SourceNorm.lp q) VoterResponseModel.modelB := by
  exact theorem2Statement_modelB h hC hUtil hResponse hdual

theorem proof_theorem2Statement_of_sourceBridge_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hSource : Theorem2SourceToFiniteSSGMBridge E)
    (hSSGM : Theorem2SSGMConvergenceTheorem E) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceBridge_ssgmConvergence hSource hSSGM

theorem proof_theorem2Statement_of_sourceBridge_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hSource : Theorem2SourceToFiniteSSGMBridge E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Theorem2SSGMConvergenceTheorem E)) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceBridge_ssgmConvergence hSource
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_theorem2Statement_of_sourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E)
    (hSSGM : Theorem2SSGMConvergenceTheorem E) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceSemantics_ssgmConvergence S hSSGM

theorem proof_theorem2Statement_of_sourceSemantics_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Theorem2SSGMConvergenceTheorem E)) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceSemantics_ssgmConvergence S
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

/--
Proof-facing Theorem 2 source semantics with probabilistic C3 noncollision.

Compared with `Theorem2PrimitiveSourceSemantics`, this record does not assume a
deterministic all-time coordinate-noncollision path.  It supplies a sampled
selected-voter process with the finite C3 ideal marginal law, and
`proof_finiteModelBILVAlgorithm1PrimitiveTraceSource_of_sampledTrace` extracts
the deterministic trace record used by the existing finite SSGM bridge.
-/
structure Theorem2SampledSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  hNorm : UsesFiniteCoordinateNormDistance E
  c3 : FiniteCoordinateC3Carrier E
  modelB_sampled_trace :
    ∀ {p q : ℝ},
      IsLpNormedUtilities E (SourceNorm.lp p) →
        E.respondsAccordingTo VoterResponseModel.modelB →
          HolderDualFinite p q →
            FiniteModelBILVAlgorithm1SampledTraceSource E p q r0 c3

noncomputable def
    proof_theorem2PrimitiveSourceSemantics_of_sampledSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SampledSourceSemantics E) :
    Theorem2PrimitiveSourceSemantics E where
  r0 := S.r0
  r0_pos := S.r0_pos
  hNorm := S.hNorm
  c3Data := S.c3.data
  modelB_primitive_trace := by
    intro p q hUtil hResponse hdual
    exact
      proof_finiteModelBILVAlgorithm1PrimitiveTraceSource_of_sampledTrace
        (S.modelB_sampled_trace hUtil hResponse hdual)

noncomputable def proof_theorem2SourceSemantics_of_sampledSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SampledSourceSemantics E) :
    Theorem2SourceSemantics E :=
  theorem2SourceSemantics_of_primitive
    (proof_theorem2PrimitiveSourceSemantics_of_sampledSourceSemantics S)

theorem proof_theorem2Statement_of_sampledSourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SampledSourceSemantics E)
    (hSSGM : Theorem2SSGMConvergenceTheorem E) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceSemantics_ssgmConvergence
    (proof_theorem2SourceSemantics_of_sampledSourceSemantics S) hSSGM

def proof_theorem2SourceSemantics_finite_bridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    Theorem2FiniteSSGMBridge E p q := by
  exact
    (theorem2SourceToFiniteSSGMBridge_of_semantics S).finite_bridge
      hC hUtil hResponse hdual

theorem proof_theorem2SourceSemantics_stepSizeConditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E) :
    SSGMStepSizeConditions (ilvRadius S.r0) := by
  exact ilvRadius_ssgmStepSizeConditions S.r0_pos

theorem proof_theorem2SourceSemantics_trajectory_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    ∀ t : ℕ,
      E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
        E.solutionSpace := by
  exact
    (proof_theorem2SourceSemantics_finite_bridge
      S hC hUtil hResponse hdual).trace.trajectory_mem_solutionSpace
        hdual S.r0_pos

theorem proof_theorem2SourceSemantics_finite_bridge_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    let B : Theorem2FiniteSSGMBridge E p q :=
      proof_theorem2SourceSemantics_finite_bridge
        S hC hUtil hResponse hdual
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - B.trace.ideal t i) =
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (B.trace.voter t) i) := by
  exact
    (proof_theorem2SourceSemantics_finite_bridge
      S hC hUtil hResponse hdual).lpCost_eq_selectedVoter_lpCost

theorem proof_proposition1Statement_modelA
    {Voter Point : Type*} {Component : Type} {E : ILVEnvironment Voter Point}
    (h : proposition1Statement E)
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter Point Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelA := by
  exact proposition1Statement_modelA h hC hWeighted hResponse

theorem proof_proposition1Statement_modelB
    {Voter Point : Type*} {Component : Type} {E : ILVEnvironment Voter Point}
    (h : proposition1Statement E)
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter Point Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelB := by
  exact proposition1Statement_modelB h hC hWeighted hResponse

theorem proof_proposition1FiniteSSGMBridge_trajectory_mem_solutionSpace
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel}
    (B : Proposition1FiniteSSGMBridge E W model) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace := by
  exact B.trajectory_mem_solutionSpace

theorem proof_proposition1Statement_of_sourceBridge_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hSource : Proposition1SourceToFiniteSSGMBridge E)
    (hSSGM : Proposition1SSGMConvergenceTheorem E) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceBridge_ssgmConvergence hSource hSSGM

theorem proof_proposition1Statement_of_sourceBridge_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hSource : Proposition1SourceToFiniteSSGMBridge E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition1SSGMConvergenceTheorem E)) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceBridge_ssgmConvergence hSource
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_proposition1Statement_of_sourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    (hSSGM : Proposition1SSGMConvergenceTheorem E) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceSemantics_ssgmConvergence S hSSGM

theorem proof_proposition1Statement_of_sourceSemantics_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition1SSGMConvergenceTheorem E)) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceSemantics_ssgmConvergence S
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

/--
Proof-facing Proposition 1 source semantics with probabilistic component
noncollision.

This record replaces the deterministic `component_noncollision` source field in
`WeightedEuclideanL2ConcreteComponentTraceSource` with a sampled selected-voter
process whose component ideals have the paper's finite-coordinate marginal laws.
`proof_weightedEuclideanL2ConcreteComponentTraceSource_of_sampledTrace` chooses
one a.e.-good path and then reuses the existing concrete component SSGM bridge.
-/
structure Proposition1ConcreteComponentSampledSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  weighted_l2_sampled_component_inputs :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
      {model : VoterResponseModel},
        ConditionsC123 E →
          IsWeightedEuclideanUtilitiesWith E W →
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                Σ r0 : ℝ,
                  WeightedEuclideanL2ConcreteComponentSampledTraceSource
                    E W model r0
  weighted_objective :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
      ConditionsC123 E →
        IsWeightedEuclideanUtilitiesWith E W →
          WeightedEuclideanSocialObjectiveFormulaSource E W

noncomputable def
    proof_proposition1ConcreteComponentSourceSemantics_of_sampledSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1ConcreteComponentSampledSourceSemantics E) :
    Proposition1ConcreteComponentSourceSemantics E where
  weighted_l2_concrete_component_inputs := by
    intro Component W model hC hW hmodel hResponse
    rcases
        S.weighted_l2_sampled_component_inputs hC hW hmodel hResponse with
      ⟨r0, T⟩
    exact
      ⟨r0,
        proof_weightedEuclideanL2ConcreteComponentTraceSource_of_sampledTrace
          T⟩
  weighted_objective := S.weighted_objective

noncomputable def
    proof_proposition1SourceSemantics_of_sampledConcreteComponentSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1ConcreteComponentSampledSourceSemantics E) :
    Proposition1SourceSemantics E :=
  proposition1SourceSemantics_of_componentSemantics
    (proposition1ComponentSourceSemantics_of_concreteComponentSemantics
      (proof_proposition1ConcreteComponentSourceSemantics_of_sampledSourceSemantics
        S))

theorem
    proof_proposition1Statement_of_sampledConcreteComponentSourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1ConcreteComponentSampledSourceSemantics E)
    (hSSGM : Proposition1SSGMConvergenceTheorem E) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceSemantics_ssgmConvergence
    (proof_proposition1SourceSemantics_of_sampledConcreteComponentSourceSemantics
      S)
    hSSGM

theorem
    proof_proposition1Statement_of_sampledConcreteComponentSourceSemantics_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1ConcreteComponentSampledSourceSemantics E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition1SSGMConvergenceTheorem E)) :
    proposition1Statement E := by
  exact
    proof_proposition1Statement_of_sampledConcreteComponentSourceSemantics_ssgmConvergence
      S (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

def proof_proposition1SourceToFiniteSSGMBridge_finite_bridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (B : Proposition1SourceToFiniteSSGMBridge E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
      Σ' _hWeightedW : IsWeightedEuclideanUtilitiesWith E W,
        Proposition1FiniteSSGMBridge E W model := by
  exact B.finite_bridge hC hWeighted model hmodel hResponse

noncomputable def proof_proposition1SourceSemantics_finite_bridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
      Σ' _hWeightedW : IsWeightedEuclideanUtilitiesWith E W,
        Proposition1FiniteSSGMBridge E W model := by
  exact
    (proposition1SourceToFiniteSSGMBridge_of_semantics S).finite_bridge
      hC hWeighted model hmodel hResponse

theorem proof_proposition1SourceSemantics_trajectory_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace := by
  rcases proof_proposition1SourceSemantics_finite_bridge
      S hC hWeighted model hmodel hResponse with
    ⟨_W, _hWeightedW, B⟩
  exact B.trajectory_mem_solutionSpace

theorem proof_proposition1SourceSemantics_stepSizeConditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] {Component : Type}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hC : ConditionsC123 E)
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    {model : VoterResponseModel}
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ∃ r0 : ℝ, SSGMStepSizeConditions (ilvRadius r0) := by
  rcases S.weighted_l2_inputs hC hW hmodel hResponse with ⟨r0, T⟩
  exact ⟨r0, ilvRadius_ssgmStepSizeConditions T.r0_pos⟩

theorem proof_proposition1SourceSemantics_socialObjective_mem_socialOptimal_iff
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] {Component : Type}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hC : ConditionsC123 E)
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    {x : Coord → ℝ} :
    x ∈ E.socialOptimal ↔
      x ∈ E.solutionSpace ∧
        IsMinOn (socialCostObjective E) E.solutionSpace x := by
  exact
    (weightedEuclideanSocialObjectiveSource_of_formulaSource
      (S.weighted_objective hC hW)).mem_socialOptimal_iff x

theorem proof_proposition2Statement_modelA
    {Voter Point : Type*} {Coord : Type} {E : ILVEnvironment Voter Point}
    (h : proposition2Statement E)
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelA := by
  exact proposition2Statement_modelA h hC hDecomposable hResponse

theorem proof_proposition2Statement_modelB
    {Voter Point : Type*} {Coord : Type} {E : ILVEnvironment Voter Point}
    (h : proposition2Statement E)
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelB := by
  exact proposition2Statement_modelB h hC hDecomposable hResponse

theorem proof_proposition2FiniteCoordinateStatement_modelA
    {Voter Coord : Type*} {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (h : proposition2FiniteCoordinateStatement E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (hCoordinate :
      ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelA := by
  exact proposition2FiniteCoordinateStatement_modelA
    h hC hD hCoordinate hResponse

theorem proof_proposition2FiniteCoordinateStatement_modelB
    {Voter Coord : Type*} {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (h : proposition2FiniteCoordinateStatement E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (hCoordinate :
      ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelB := by
  exact proposition2FiniteCoordinateStatement_modelB
    h hC hD hCoordinate hResponse

theorem proof_proposition2Statement_of_sourceBridge_ssgmConvergence
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hSource : Proposition2SourceToSSGMBridge E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2Statement E := by
  exact proposition2Statement_of_sourceBridge_ssgmConvergence hSource hSSGM

theorem proof_proposition2Statement_of_sourceBridge_ssgmBoundary
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hSource : Proposition2SourceToSSGMBridge E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition2SSGMConvergenceTheorem E)) :
    proposition2Statement E := by
  exact proposition2Statement_of_sourceBridge_ssgmConvergence hSource
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_proposition2Statement_of_sourceSemantics_ssgmConvergence
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2Statement E := by
  exact proposition2Statement_of_sourceSemantics_ssgmConvergence S hSSGM

theorem proof_proposition2_fixedDecomposition_convergence_of_sourceSemantics_ssgmConvergence
    {Voter Point : Type*} {Coord : Type} {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (S : Proposition2FixedSourceSemantics E D)
    (hSSGM : Proposition2SSGMConvergenceTheorem E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ILVConvergesToMedianSet E SourceNorm.linfty model := by
  exact
    proposition2_fixedDecomposition_convergence_of_sourceSemantics_ssgmConvergence
      S hSSGM hC hD model hmodel hResponse

theorem proof_proposition2_fixedDecomposition_convergence_of_finiteCoordinateSourceSemantics_ssgmConvergence
    {Voter : Type*} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (S : Proposition2FiniteCoordinateFixedSourceSemantics E D)
    (hSSGM : Proposition2SSGMConvergenceTheorem E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ILVConvergesToMedianSet E SourceNorm.linfty model := by
  exact
    proposition2_fixedDecomposition_convergence_of_finiteCoordinateSourceSemantics_ssgmConvergence
      S hSSGM hC hD model hmodel hResponse

theorem proof_proposition2FiniteCoordinateStatement_of_finiteCoordinateSourceSemantics_ssgmConvergence
    {Voter : Type*} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition2FiniteCoordinateSourceSemantics E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2FiniteCoordinateStatement E := by
  exact
    proposition2FiniteCoordinateStatement_of_finiteCoordinateSourceSemantics_ssgmConvergence
      S hSSGM

theorem proof_proposition2Statement_of_sourceSemantics_ssgmBoundary
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition2SSGMConvergenceTheorem E)) :
    proposition2Statement E := by
  exact proposition2Statement_of_sourceSemantics_ssgmConvergence S
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

def proof_proposition2SourceToSSGMBridge_case_certificate
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (B : Proposition2SourceToSSGMBridge E)
    {Coord : Type}
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ D : DecomposableStructure Voter Point Coord,
      Proposition2SSGMCaseCertificate E D model := by
  exact B.case_certificate hC hDecomposable model hmodel hResponse

noncomputable def proof_proposition2SourceSemantics_case_certificate
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E)
    {Coord : Type}
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ D : DecomposableStructure Voter Point Coord,
      Proposition2SSGMCaseCertificate E D model := by
  exact
    (proposition2SourceToSSGMBridge_of_semantics S).case_certificate
      hC hDecomposable model hmodel hResponse

theorem proof_theorem2Statement_of_concreteSourceModel_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Theorem2SSGMConvergenceTheorem E)) :
    theorem2Statement E := by
  exact theorem2Statement_of_concreteSourceModel_ssgmConvergence M
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_proposition1Statement_of_concreteSourceModel_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition1SSGMConvergenceTheorem E)) :
    proposition1Statement E := by
  exact proposition1Statement_of_concreteSourceModel_ssgmConvergence M
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_proposition2Statement_of_concreteSourceModel_ssgmBoundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hBoundary :
      EconCSLib.Optimization.SSGMConvergenceBoundary
        (Proposition2SSGMConvergenceTheorem E)) :
    proposition2Statement E := by
  exact proposition2Statement_of_concreteSourceModel_ssgmConvergence M
    (EconCSLib.Optimization.SSGMConvergenceBoundary.elim hBoundary)

theorem proof_theorem3Statement_directionalEquilibrium
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem3Statement E)
    (hG : Theorem3DirectionalFieldFormula E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Point}
    (hConverges :
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3Statement_directionalEquilibrium
    h hG hC hContinuous hResponse hConverges

theorem proof_weightedEuclideanUtilityFormula_eq_neg_sum
    {Voter Point Component : Type*}
    (W : WeightedEuclideanStructure Voter Point Component)
    (v : Voter) (x : Point) :
    weightedEuclideanUtilityFormula W v x =
      -W.components.sum
        (fun k =>
          (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v) := by
  exact weightedEuclideanUtilityFormula_eq_neg_sum W v x

theorem proof_isWeightedEuclideanUtilitiesWith_condition
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (h : IsWeightedEuclideanUtilitiesWith E W) :
    W.weightsAndIdealsDistributionCondition := by
  exact h.weightsAndIdealsDistributionCondition

theorem proof_isWeightedEuclideanUtilitiesWith_utility_eq_formula
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (h : IsWeightedEuclideanUtilitiesWith E W)
    (v : Voter) (x : Point) :
    E.utility v x = weightedEuclideanUtilityFormula W v x := by
  exact h.utility_eq_formula v x

theorem proof_isWeightedEuclideanUtilitiesWith_utility_eq_neg_sum
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (h : IsWeightedEuclideanUtilitiesWith E W)
    (v : Voter) (x : Point) :
    E.utility v x =
      -W.components.sum
        (fun k =>
          (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v) := by
  exact h.utility_eq_neg_sum v x

theorem proof_isWeightedEuclideanUtilitiesWith_intro_formula
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (hcondition : W.weightsAndIdealsDistributionCondition)
    (hformula :
      ∀ v x, E.utility v x = weightedEuclideanUtilityFormula W v x) :
    IsWeightedEuclideanUtilitiesWith E W := by
  exact IsWeightedEuclideanUtilitiesWith.intro_formula hcondition hformula

theorem proof_decomposableUtilityFormula_eq_sum
    {Voter Point Coord : Type*}
    (D : DecomposableStructure Voter Point Coord)
    (v : Voter) (x : Point) :
    decomposableUtilityFormula D v x =
      D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x)) := by
  exact decomposableUtilityFormula_eq_sum D v x

theorem proof_isDecomposableUtilitiesWith_concavity
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (h : IsDecomposableUtilitiesWith E D) :
    D.coordinateUtilitiesConcave := by
  exact h.coordinateUtilitiesConcave

theorem proof_isDecomposableUtilitiesWith_utility_eq_formula
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (h : IsDecomposableUtilitiesWith E D)
    (v : Voter) (x : Point) :
    E.utility v x = decomposableUtilityFormula D v x := by
  exact h.utility_eq_formula v x

theorem proof_isDecomposableUtilitiesWith_utility_eq_sum
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (h : IsDecomposableUtilitiesWith E D)
    (v : Voter) (x : Point) :
    E.utility v x =
      D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x)) := by
  exact h.utility_eq_sum v x

theorem proof_isDecomposableUtilitiesWith_intro_formula
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (hconcave : D.coordinateUtilitiesConcave)
    (hformula : ∀ v x, E.utility v x = decomposableUtilityFormula D v x) :
    IsDecomposableUtilitiesWith E D := by
  exact IsDecomposableUtilitiesWith.intro_formula hconcave hformula

theorem proof_weightedEuclideanL2SSGMInputs_trajectory_mem_solutionSpace
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (C : WeightedEuclideanL2SSGMInputs E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace := by
  exact C.trajectory_mem_solutionSpace

theorem proof_weightedEuclideanL2SSGMInputs_stepSizeConditions
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (C : WeightedEuclideanL2SSGMInputs E W model r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact C.ssgmStepSizeConditions

theorem proof_weightedEuclideanSocialObjectiveBridge_mem_socialOptimal_iff
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (C : WeightedEuclideanSocialObjectiveBridge E W) {x : Coord → ℝ} :
    x ∈ E.socialOptimal ↔
      x ∈ E.solutionSpace ∧ IsMinOn C.objective E.solutionSpace x := by
  exact C.mem_socialOptimal_iff

theorem proof_decomposableMedianCarrier_mem_medianSet_iff
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (C : DecomposableMedianCarrier E D) {x : Point} :
    x ∈ E.medianSet ↔
      ∀ m, m ∈ D.coords →
        D.coordinate m x ∈ C.coordinateMedianSet m := by
  exact C.mem_medianSet_iff

theorem proof_decomposableLinfLocalResponseBridge_of_coordinateReplacement
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (hD : IsDecomposableUtilitiesWith E D)
    (R : DecomposableLinfCoordinateReplacement E D) :
    DecomposableLinfLocalResponseBridge E D := by
  exact decomposableLinfLocalResponseBridge_of_coordinateReplacement hD R

noncomputable def proof_decomposableLinfCoordinateReplacement_of_finiteCoordinate
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (S : FiniteCoordinateLinfCoordinateReplacementSource E D) :
    DecomposableLinfCoordinateReplacement E D :=
  decomposableLinfCoordinateReplacement_of_finiteCoordinate S

noncomputable def proof_proposition2FixedSourceSemantics_of_medianSetSource_productBox
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (hMedian :
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableMedianSetSource E D)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hProductBox : FiniteCoordinateProductBoxSolutionSpaceSource E)
    (hCoordinate :
      ∀ m : Coord, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m) :
    Proposition2FixedSourceSemantics E D :=
  proposition2FixedSourceSemantics_of_medianSetSource_productBox
    hMedian hNorm hProductBox hCoordinate

theorem proof_proposition2FixedSourceSemantics_mem_medianSet_iff
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (S : Proposition2FixedSourceSemantics E D)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    {x : Point} :
    x ∈ E.medianSet ↔
      ∀ m, m ∈ D.coords →
        D.coordinate m x ∈ (S.medianSetSource hC hD).coordinateMedianSet m := by
  exact (S.medianSetSource hC hD).mem_medianSet_iff x

theorem proof_proposition2FixedSourceSemantics_coordinate_response_isMaxOn
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (S : Proposition2FixedSourceSemantics E D)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    {center response : Point} {r : ℝ} {voter : Voter}
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (m : Coord) (hm : m ∈ D.coords) :
    IsMaxOn
      (fun z : ℝ => D.coordinateUtility m voter z)
      {z | ∃ candidate,
        candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
          D.coordinate m candidate = z}
      (D.coordinate m response) := by
  exact (S.linfResponse hC hD).coordinate_response_isMaxOn hresponse m hm

theorem proof_decomposableLinfLocalResponseBridge_coordinate_response_isMaxOn
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (C : DecomposableLinfLocalResponseBridge E D)
    {center response : Point} {r : ℝ} {voter : Voter}
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (m : Coord) (hm : m ∈ D.coords) :
    IsMaxOn
      (fun z : ℝ => D.coordinateUtility m voter z)
      {z | ∃ candidate,
        candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
          D.coordinate m candidate = z}
      (D.coordinate m response) := by
  exact C.coordinate_response_isMaxOn hresponse m hm

theorem proof_convergentModelBDriftCertificate_isDirectionalEquilibrium
    {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} {xstar : Point}
    (C : ConvergentModelBDriftCertificate E xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact C.isDirectionalEquilibrium

theorem proof_theorem3Statement_of_deterministicBridge
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (B : Theorem3DeterministicBridge E) :
    theorem3Statement E := by
  exact theorem3Statement_of_deterministicBridge B

/--
Proof-facing finite-coordinate analytic route for Theorem 3.

This is intentionally not a paper-facing endpoint row: the finite directional
field and accumulated-drift semantics are proof certificates that still need to
be derived from the paper's concrete Model B source behavior before the final
paper route is assumption-clean.
-/
theorem proof_theorem3_finite_analytic_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3AnalyticDriftSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3Statement_directionalEquilibrium
    (theorem3Statement_of_deterministicBridge
      (theorem3DeterministicBridge_of_analyticDriftSemantics
        (FiniteTheorem3AnalyticDriftSemantics.toAnalyticDriftSemantics D)))
    (theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel G)
    hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from one-step projected progress.  This is the
preferred continuation point for eliminating the old environment-level drift
field: prove the local Model B projected-progress inequality, then Lean
telescopes it into the accumulated contradiction.
-/
theorem proof_theorem3_finite_oneStep_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3OneStepDriftSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3Statement_directionalEquilibrium
    (theorem3Statement_of_deterministicBridge
      (theorem3DeterministicBridge_of_finiteOneStepDriftSemantics D))
    (theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel G)
    hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from paper-radius projected progress.  Compared
with `proof_theorem3_finite_oneStep_directionalEquilibrium`, this fixes the
tail radius to Algorithm 1's source step size `r0 / t`; Lean proves the
divergent-radius accumulation internally.
-/
theorem proof_theorem3_finite_paperRadius_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3PaperRadiusDriftSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3Statement_directionalEquilibrium
    (theorem3Statement_of_deterministicBridge
      (theorem3DeterministicBridge_of_finitePaperRadiusDriftSemantics D))
    (theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel G)
    hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from eventual concrete paper-radius projected
escape with explicit finite-coordinate convergence.  This matches the paper's
near-the-limit drift shape: once the trajectory is close enough to a putative
non-equilibrium limit, accumulated projected progress contradicts convergence.
-/
theorem proof_theorem3_finite_paperRadiusEventualEscape_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperRadiusEventualEscapeSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from finite-dot scalar drift plus eventual
Hoeffding/fluctuation control.  This is the scalar-projection counterpart to the
coordinate Hoeffding shell and maps directly into the concrete paper-radius
projected escape endpoint.
-/
theorem proof_theorem3_finite_finiteDotEventualHoeffdingShell_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotEventualHoeffdingShell
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from finite-dot scalar
Hoeffding/fluctuation control.  Lean derives the eventual positive scalar drift
from coordinate-continuity of the concrete field and trajectory convergence.
-/
theorem proof_theorem3_finite_finiteDotHoeffdingShell_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotHoeffdingShell
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from raw finite-voter Model B response scalar
fluctuation control.  Lean identifies the raw expected finite-dot increments
with the projected-progress field terms and derives the positive scalar drift.
-/
theorem proof_theorem3_finite_finiteDotSampledRawHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotSampledRawHoeffding
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from exact sampled raw finite-dot increments.  Lean
telescopes the scalar projection and converts this to the projected finite-dot
route with zero projection slack.
-/
theorem proof_theorem3_finite_finiteDotExactSampledRawHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotExactSampledRawHoeffding
    G D hC hContinuous hResponse hConverges

/--
Exact finite-dot sampled raw increments are the zero-slack special case of the
projected finite-dot shell.  This exposes the deterministic projection
telescoping bridge without closing the remaining projected-source concentration
and slack obligations.
-/
noncomputable def proof_theorem3_finite_finiteDotExactSampledRaw_to_projectedRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics G) :
    FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics G :=
  FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics.toProjectedRawHoeffdingSemantics
    D

/-- Finite-dimensional Cauchy-Schwarz for the paper-local finite-dot product. -/
theorem proof_theorem3_finiteDot_abs_le_l2_mul_l2
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    |finiteDot x y| ≤
      finiteCoordinateNorm SourceNorm.l2 x *
        finiteCoordinateNorm SourceNorm.l2 y := by
  exact finiteDot_abs_le_l2_mul_l2 x y

/--
Increment form of finite-dimensional Cauchy-Schwarz for selected finite-dot
raw increments.
-/
theorem proof_theorem3_finiteDot_increment_abs_le_l2_mul_distance
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a x y : Coord → ℝ) :
    |finiteDot a (fun i => y i - x i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a *
        finiteCoordinateDistance SourceNorm.l2 y x := by
  exact finiteDot_increment_abs_le_l2_mul_distance a x y

/-- Bounded-step finite-dot increment corollary for Hoeffding/Azuma inputs. -/
theorem proof_theorem3_finiteDot_increment_abs_le_l2_mul_stepBound
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a x y : Coord → ℝ) {R : ℝ}
    (hstep : finiteCoordinateDistance SourceNorm.l2 y x ≤ R) :
    |finiteDot a (fun i => y i - x i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a * R := by
  exact finiteDot_increment_abs_le_l2_mul_stepBound a x y hstep

theorem proof_theorem3_modelBFiniteNormalizedDirection_l2_norm_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (gradient : Coord → ℝ) :
    finiteCoordinateNorm SourceNorm.l2
        (modelBFiniteNormalizedDirection SourceNorm.l2 gradient) ≤ 1 := by
  exact modelBFiniteNormalizedDirection_l2_norm_le_one gradient

theorem proof_theorem3_modelBFiniteResponseAt_l2_within_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center gradient response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hresponse :
      ModelBFiniteResponseAt SourceNorm.l2 center r gradient response) :
    finiteCoordinateDistance SourceNorm.l2 response center ≤ r := by
  exact modelBFiniteResponseAt_l2_within_radius hr hresponse

theorem proof_theorem3_finiteDot_modelB_response_increment_abs_le_l2_mul_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a center gradient response : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (hresponse :
      ModelBFiniteResponseAt SourceNorm.l2 center r gradient response) :
    |finiteDot a (fun i => response i - center i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a * r := by
  exact finiteDot_modelB_response_increment_abs_le_l2_mul_radius
    a center gradient response hr hresponse

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_mem_Icc
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter))
    (selected : Voter) :
    finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i)) ∈
      Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * r)) := by
  exact finiteDot_modelB_centered_response_increment_mem_Icc
    weight hweight_nonneg hweight_sum a center hr utilityGradient response
    hresponse selected

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_mem_Icc_sequence
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i)) ∈
      Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) := by
  exact finiteDot_modelB_centered_response_increment_mem_Icc_sequence
    weight hweight_nonneg hweight_sum a center radius hradius_nonneg
    utilityGradient response sampledVoter hresponse t

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_mem_Icc_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i)) ∈
      Set.Icc
        (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))) := by
  exact finiteDot_modelB_centered_response_increment_mem_Icc_ilvRadius
    weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
    sampledVoter hresponse t

theorem proof_abs_le_of_mem_Icc_neg {x c : ℝ}
    (h : x ∈ Set.Icc (-c) c) :
    |x| ≤ c := by
  exact abs_le_of_mem_Icc_neg h

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_abs_le
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter))
    (selected : Voter) :
    |finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * r) := by
  exact finiteDot_modelB_centered_response_increment_abs_le
    weight hweight_nonneg hweight_sum a center hr utilityGradient response
    hresponse selected

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_abs_le_sequence
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    |finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t) := by
  exact finiteDot_modelB_centered_response_increment_abs_le_sequence
    weight hweight_nonneg hweight_sum a center radius hradius_nonneg
    utilityGradient response sampledVoter hresponse t

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_abs_le_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    |finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1)) := by
  exact finiteDot_modelB_centered_response_increment_abs_le_ilvRadius
    weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
    sampledVoter hresponse t

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : Coord → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (t : ℕ) :
    0 ≤ 2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1)) := by
  exact finiteDot_modelB_centered_response_increment_ilvRadius_bound_nonneg
    a hr0 t

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : Coord → ℝ) (r0 : ℝ) :
    Summable
      (fun t : ℕ =>
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))) ^ 2) := by
  exact finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable
    a r0

/--
Concrete Model B selected-voter increment route for the martingale fluctuation
lemma.  The remaining stochastic-process obligations are exposed explicitly:
the partial-sum process must be past-adapted, increments must be measurable and
conditionally mean-zero, and the increment process must agree a.e. with the
paper's centered selected-voter finite-dot increment.  From those facts Lean
derives the `ilvRadius` absolute bound and square-summability.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_modelB_ilvRadius_process
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration (Ω := Ω) ℕ mΩ}
    {expected realized : ℕ → Ω → ℝ} {base : ℝ}
    (hadapted_sum :
      StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, Y i ω))
    (hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0)
    (hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ)
    (hY_eq :
      ∀ n : ℕ,
        ∀ᵐ ω ∂μ,
          Y n ω =
            finiteDot a
              (fun i => response n (sampledVoter n) i - center n i) -
              (∑ voter : Voter,
                weight voter *
                  finiteDot a (fun i => response n voter i - center n i)))
    (hcentered :
      ∀ n ω,
        expected n ω - base - realized n ω =
          ∑ i ∈ Finset.range n, Y i ω) :
    ∀ᵐ ω ∂μ,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n ω - fluctuationBound ≤ base + realized n ω := by
  let c : ℕ → ℝ :=
    fun t => 2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))
  have hc : ∀ n : ℕ, 0 ≤ c n := by
    intro n
    exact
      proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_nonneg
        a hr0 n
  have hY_abs_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Y n ω| ≤ c n := by
    intro n
    filter_upwards [hY_eq n] with ω hω
    dsimp [c]
    rw [hω]
    exact
      proof_theorem3_finiteDot_modelB_centered_response_increment_abs_le_ilvRadius
        weight hweight_nonneg hweight_sum a center hr0 utilityGradient
        response sampledVoter hresponse n
  have hsummable_sq : Summable fun n : ℕ => (c n) ^ 2 := by
    simpa [c] using
      proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable
        a r0
  exact
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_summable_partialSumAdapted
      (μ := μ) (Y := Y) (c := c) (ℱ := ℱ)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hcond_zero hY_aemeas hc hY_abs_bound hsummable_sq
      hcentered

theorem proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
    {Voter : Type*} [Fintype Voter] [MeasurableSpace Voter]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1) :
    IsProbabilityMeasure
      (theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum) := by
  let P : ℕ → Measure Voter :=
    fun _ =>
      (EconCSLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure
  have hμ : ∀ i : ℕ, IsProbabilityMeasure (P i) := by
    intro i
    exact inferInstance
  simpa [theorem3FiniteWeightedVoterSequenceMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ℕ) (X := fun _ : ℕ => Voter)
      (mX := fun _ => by infer_instance) (μ := P) hμ

theorem proof_theorem3_finiteWeightedVoterSequence_coordinate_iIndepFun
    {Voter : Type*} [Fintype Voter] [MeasurableSpace Voter]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1) :
    ProbabilityTheory.iIndepFun
      (fun t (sample : ℕ → Voter) => sample t)
      (theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum) := by
  let P : ℕ → Measure Voter :=
    fun _ =>
      (EconCSLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure
  have hμ : ∀ i : ℕ, IsProbabilityMeasure (P i) := by
    intro i
    exact inferInstance
  have hcoord :
      ProbabilityTheory.iIndepFun (fun t (sample : ℕ → Voter) => sample t)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := ℕ) (𝓧 := fun _ : ℕ => Voter)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ : ℕ => Voter) (mΩ := fun _ => by infer_instance)
        (P := P) hμ (X := fun _ : ℕ => fun voter : Voter => voter)
        (mX := fun _ => measurable_id)
  simpa [theorem3FiniteWeightedVoterSequenceMeasure, P] using hcoord

/-- The centered finite-dot increment as a function of the selected voter. -/
noncomputable def theorem3FiniteDotCenteredIncrement
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord]
    (weight : Voter → ℝ)
    (a center : Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (selected : Voter) : ℝ :=
  finiteDot a (fun i => response selected i - center i) -
    (∑ voter : Voter,
      weight voter * finiteDot a (fun i => response voter i - center i))

theorem proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_iIndepFun
    {Voter Coord : Type*} [Fintype Voter] [MeasurableSpace Voter]
    [MeasurableSingletonClass Voter] [Fintype Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ) :
    ProbabilityTheory.iIndepFun
      (fun t (sample : ℕ → Voter) =>
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) (sample t))
      (theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum) := by
  exact
    (proof_theorem3_finiteWeightedVoterSequence_coordinate_iIndepFun
      weight hweight_nonneg hweight_sum).comp
      (fun t selected =>
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) selected)
      (fun _ => measurable_of_finite _)

theorem proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_aemeasurable
    {Voter Coord : Type*} [Fintype Voter] [MeasurableSpace Voter]
    [MeasurableSingletonClass Voter] [Fintype Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (t : ℕ) :
    AEStronglyMeasurable
      (fun sample : ℕ → Voter =>
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) (sample t))
      (theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum) := by
  exact
    (((measurable_of_finite
      (theorem3FiniteDotCenteredIncrement weight a (center t)
        (response t))).comp (measurable_pi_apply t))).aestronglyMeasurable

theorem proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_stronglyMeasurable
    {Voter Coord : Type*} [Fintype Voter] [MeasurableSpace Voter]
    [MeasurableSingletonClass Voter] [Fintype Coord]
    (weight : Voter → ℝ)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (t : ℕ) :
    StronglyMeasurable
      (fun sample : ℕ → Voter =>
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) (sample t)) := by
  exact
    (((measurable_of_finite
      (theorem3FiniteDotCenteredIncrement weight a (center t)
        (response t))).comp (measurable_pi_apply t))).stronglyMeasurable

theorem
    proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_succ_partial_sum_stronglyAdapted_natural
    {Voter Coord : Type*} [Fintype Voter] [MeasurableSpace Voter]
    [MeasurableSingletonClass Voter] [Fintype Coord]
    (weight : Voter → ℝ)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hX_sm :
      ∀ t : ℕ,
        StronglyMeasurable
          (fun sample : ℕ → Voter =>
            theorem3FiniteDotCenteredIncrement weight a (center t)
              (response t) (sample t))) :
    StronglyAdapted
      (Filtration.natural
        (fun t (sample : ℕ → Voter) =>
          theorem3FiniteDotCenteredIncrement weight a (center t)
            (response t) (sample t)) hX_sm)
      (fun n (sample : ℕ → Voter) =>
        ∑ i ∈ Finset.range n,
          theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
            (response (i + 1)) (sample (i + 1))) := by
  exact
    proof_probability_shifted_partial_sum_stronglyAdapted_natural
      (X := fun t (sample : ℕ → Voter) =>
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) (sample t)) hX_sm

theorem proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_integral_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (t : ℕ) :
    (∫ sample : ℕ → Voter,
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) (sample t)
      ∂theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum) = 0 := by
  let μv : PMF Voter :=
    EconCSLib.finiteWeightedPMF weight hweight_nonneg
      (by simpa [hweight_sum] using zero_lt_one)
  let P : ℕ → Measure Voter := fun _ => μv.toMeasure
  let F : Voter → ℝ :=
    theorem3FiniteDotCenteredIncrement weight a (center t) (response t)
  have hμ : ∀ i : ℕ, IsProbabilityMeasure (P i) := by
    intro i
    exact inferInstance
  have hF :
      AEStronglyMeasurable F
        (Measure.map (fun sample : ℕ → Voter => sample t)
          (theorem3FiniteWeightedVoterSequenceMeasure
            weight hweight_nonneg hweight_sum)) :=
    (measurable_of_finite F).aestronglyMeasurable
  have hmap :
      Measure.map (fun sample : ℕ → Voter => sample t)
          (theorem3FiniteWeightedVoterSequenceMeasure
            weight hweight_nonneg hweight_sum) =
        μv.toMeasure := by
    simpa [theorem3FiniteWeightedVoterSequenceMeasure, P, μv] using
      (@MeasureTheory.Measure.infinitePi_map_eval
        (ι := ℕ) (X := fun _ : ℕ => Voter)
        (mX := fun _ => by infer_instance) (μ := P) hμ t)
  calc
    (∫ sample : ℕ → Voter,
        theorem3FiniteDotCenteredIncrement weight a (center t)
          (response t) (sample t)
      ∂theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum)
        = ∫ selected : Voter, F selected
            ∂Measure.map (fun sample : ℕ → Voter => sample t)
              (theorem3FiniteWeightedVoterSequenceMeasure
                weight hweight_nonneg hweight_sum) := by
            exact
              (integral_map
                (μ := theorem3FiniteWeightedVoterSequenceMeasure
                  weight hweight_nonneg hweight_sum)
                (φ := fun sample : ℕ → Voter => sample t)
                (f := F) (measurable_pi_apply t).aemeasurable hF).symm
    _ = ∫ selected : Voter, F selected ∂μv.toMeasure := by
            rw [hmap]
    _ = 0 := by
            simpa [F, theorem3FiniteDotCenteredIncrement, μv] using
              finiteDot_modelB_centered_response_increment_integral_toMeasure_eq_zero
                weight hweight_nonneg hweight_sum a (center t) (response t)

theorem
    proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_condExp_succ_natural_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hX_sm :
      ∀ t : ℕ,
        StronglyMeasurable
          (fun sample : ℕ → Voter =>
            theorem3FiniteDotCenteredIncrement weight a (center t)
              (response t) (sample t))) :
    ∀ n : ℕ,
      (theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum)[
          (fun sample : ℕ → Voter =>
            theorem3FiniteDotCenteredIncrement weight a (center (n + 1))
              (response (n + 1)) (sample (n + 1))) |
          Filtration.natural
            (fun t (sample : ℕ → Voter) =>
              theorem3FiniteDotCenteredIncrement weight a (center t)
                (response t) (sample t)) hX_sm n] =ᵐ[
        theorem3FiniteWeightedVoterSequenceMeasure
          weight hweight_nonneg hweight_sum] 0 := by
  have hX_indep :
      ProbabilityTheory.iIndepFun
        (fun t (sample : ℕ → Voter) =>
          theorem3FiniteDotCenteredIncrement weight a (center t)
            (response t) (sample t))
        (theorem3FiniteWeightedVoterSequenceMeasure
          weight hweight_nonneg hweight_sum) :=
    proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_iIndepFun
      weight hweight_nonneg hweight_sum a center response
  have hmean_zero :
      ∀ n : ℕ,
        (∫ sample : ℕ → Voter,
          theorem3FiniteDotCenteredIncrement weight a (center (n + 1))
            (response (n + 1)) (sample (n + 1))
          ∂theorem3FiniteWeightedVoterSequenceMeasure
            weight hweight_nonneg hweight_sum) = 0 := by
    intro n
    exact
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_integral_eq_zero
        weight hweight_nonneg hweight_sum a center response (n + 1)
  exact
    proof_probability_iIndepFun_condExp_succ_natural_ae_eq_zero
      (μ := theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum)
      hX_sm hX_indep hmean_zero

theorem
    proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable_shift
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : Coord → ℝ) (r0 : ℝ) :
    Summable
      (fun n : ℕ =>
        (2 * (finiteCoordinateNorm SourceNorm.l2 a *
          ilvRadius r0 ((n + 1) + 1))) ^ 2) := by
  let f : ℕ → ℝ :=
    fun t => (2 * (finiteCoordinateNorm SourceNorm.l2 a *
      ilvRadius r0 (t + 1))) ^ 2
  have hf : Summable f := by
    simpa [f] using
      proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable
        a r0
  simpa [f, Nat.add_assoc] using
    ((summable_nat_add_iff (f := f) 1).mpr hf)

/--
Concrete product-space concentration for the paper's weighted voter draws,
in the martingale convention where the time-`n` partial sum conditions on the
first `n` centered increments and the next increment is indexed by `n+1`.

This discharges the selected-voter finite-dot fluctuation from the explicit
weighted product law, finite Model B response bounds, and the already-proved
finite weighted mean-zero identity.  The remaining indexing shift is only the
standard past-filtration convention; no SSGM theorem is used.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_ilvRadius_shifted
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    {expected realized : ℕ → (ℕ → Voter) → ℝ} {base : ℝ}
    (hcentered :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1))) :
    ∀ᵐ sample ∂theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n sample - fluctuationBound ≤ base + realized n sample := by
  let μ : Measure (ℕ → Voter) :=
    theorem3FiniteWeightedVoterSequenceMeasure
      weight hweight_nonneg hweight_sum
  haveI : IsProbabilityMeasure μ :=
    proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
      weight hweight_nonneg hweight_sum
  let X : ℕ → (ℕ → Voter) → ℝ :=
    fun t sample =>
      theorem3FiniteDotCenteredIncrement weight a (center t)
        (response t) (sample t)
  have hX_sm : ∀ t : ℕ, StronglyMeasurable (X t) := by
    intro t
    simpa [X] using
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_stronglyMeasurable
        weight a center response t
  let ℱ : Filtration (Ω := ℕ → Voter) ℕ inferInstance :=
    Filtration.natural X hX_sm
  let Y : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => X (n + 1) sample
  let c : ℕ → ℝ :=
    fun n => 2 * (finiteCoordinateNorm SourceNorm.l2 a *
      ilvRadius r0 ((n + 1) + 1))
  have hadapted_sum :
      StronglyAdapted ℱ (fun n sample => ∑ i ∈ Finset.range n, Y i sample) := by
    simpa [ℱ, Y, X] using
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_succ_partial_sum_stronglyAdapted_natural
        weight a center response hX_sm
  have hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0 := by
    simpa [μ, ℱ, Y, X] using
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_condExp_succ_natural_eq_zero
        weight hweight_nonneg hweight_sum a center response hX_sm
  have hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ := by
    intro n
    exact (hX_sm (n + 1)).aestronglyMeasurable
  have hc : ∀ n : ℕ, 0 ≤ c n := by
    intro n
    simpa [c] using
      proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_nonneg
        a hr0 (n + 1)
  have hY_abs_bound : ∀ n : ℕ, ∀ᵐ sample ∂μ, |Y n sample| ≤ c n := by
    intro n
    exact Filter.Eventually.of_forall fun sample => by
      simpa [Y, X, c, theorem3FiniteDotCenteredIncrement] using
        proof_theorem3_finiteDot_modelB_centered_response_increment_abs_le_ilvRadius
          weight hweight_nonneg (le_of_eq hweight_sum) a center hr0
          utilityGradient response sample hresponse (n + 1)
  have hsummable_sq : Summable fun n : ℕ => (c n) ^ 2 := by
    simpa [c] using
      proof_theorem3_finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable_shift
        a r0
  have hcentered' :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n, Y i sample := by
    intro n sample
    simpa [Y, X] using hcentered n sample
  simpa [μ] using
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_summable_partialSumAdapted
      (μ := μ) (Y := Y) (c := c) (ℱ := ℱ)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hcond_zero hY_aemeas hc hY_abs_bound hsummable_sq
      hcentered'

/-- Split a zero-based finite sum into its first term and shifted tail. -/
theorem proof_sum_range_succ_sub_first_eq_shifted_tail
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) - f 0 =
      ∑ i ∈ Finset.range n, f (i + 1) := by
  rw [Finset.sum_range_succ']
  ring

/--
Product-space concentration for weighted voter draws with an arbitrary
nonnegative square-summable radius schedule.  This is the reusable version of
the shifted martingale convention used by the paper's Theorem 3 tail argument.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_radius_shifted
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (hradius_sq_summable :
      Summable
        (fun t : ℕ =>
          (2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) ^ 2))
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (radius t)
          (utilityGradient voter (center t)) (response t voter))
    {expected realized : ℕ → (ℕ → Voter) → ℝ} {base : ℝ}
    (hcentered :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1))) :
    ∀ᵐ sample ∂theorem3FiniteWeightedVoterSequenceMeasure
        weight hweight_nonneg hweight_sum,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n sample - fluctuationBound ≤ base + realized n sample := by
  let μ : Measure (ℕ → Voter) :=
    theorem3FiniteWeightedVoterSequenceMeasure
      weight hweight_nonneg hweight_sum
  haveI : IsProbabilityMeasure μ :=
    proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
      weight hweight_nonneg hweight_sum
  let X : ℕ → (ℕ → Voter) → ℝ :=
    fun t sample =>
      theorem3FiniteDotCenteredIncrement weight a (center t)
        (response t) (sample t)
  have hX_sm : ∀ t : ℕ, StronglyMeasurable (X t) := by
    intro t
    simpa [X] using
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_stronglyMeasurable
        weight a center response t
  let ℱ : Filtration (Ω := ℕ → Voter) ℕ inferInstance :=
    Filtration.natural X hX_sm
  let Y : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => X (n + 1) sample
  let c : ℕ → ℝ :=
    fun n => 2 * (finiteCoordinateNorm SourceNorm.l2 a * radius (n + 1))
  have hadapted_sum :
      StronglyAdapted ℱ (fun n sample => ∑ i ∈ Finset.range n, Y i sample) := by
    simpa [ℱ, Y, X] using
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_succ_partial_sum_stronglyAdapted_natural
        weight a center response hX_sm
  have hcond_zero :
      ∀ n : ℕ, μ[Y n | ℱ n] =ᵐ[μ] 0 := by
    simpa [μ, ℱ, Y, X] using
      proof_theorem3_finiteWeightedVoterSequence_centeredIncrement_condExp_succ_natural_eq_zero
        weight hweight_nonneg hweight_sum a center response hX_sm
  have hY_aemeas :
      ∀ n : ℕ, AEStronglyMeasurable (Y n) μ := by
    intro n
    exact (hX_sm (n + 1)).aestronglyMeasurable
  have hc : ∀ n : ℕ, 0 ≤ c n := by
    intro n
    exact mul_nonneg (by norm_num)
      (mul_nonneg (finiteCoordinateNorm_l2_nonneg a)
        (hradius_nonneg (n + 1)))
  have hY_abs_bound : ∀ n : ℕ, ∀ᵐ sample ∂μ, |Y n sample| ≤ c n := by
    intro n
    exact Filter.Eventually.of_forall fun sample => by
      simpa [Y, X, c, theorem3FiniteDotCenteredIncrement] using
        proof_theorem3_finiteDot_modelB_centered_response_increment_abs_le_sequence
          weight hweight_nonneg (le_of_eq hweight_sum) a center radius
          hradius_nonneg utilityGradient response sample hresponse (n + 1)
  have hsummable_sq : Summable fun n : ℕ => (c n) ^ 2 := by
    simpa [c] using
      ((summable_nat_add_iff
        (f := fun t : ℕ =>
          (2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) ^ 2) 1).mpr
        hradius_sq_summable)
  have hcentered' :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n, Y i sample := by
    intro n sample
    simpa [Y, X] using hcentered n sample
  simpa [μ] using
    proof_theorem3_finiteDot_eventual_fluctuation_of_condExp_zero_boundedIncrement_summable_partialSumAdapted
      (μ := μ) (Y := Y) (c := c) (ℱ := ℱ)
      (expected := expected) (realized := realized) (base := base)
      hadapted_sum hcond_zero hY_aemeas hc hY_abs_bound hsummable_sq
      hcentered'

/--
Unshifted concentration for weighted voter draws with an arbitrary
nonnegative square-summable radius schedule.  The first centered increment is
absorbed into the eventual fluctuation bound, as in the paper-radius version.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_radius
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (hradius_sq_summable :
      Summable
        (fun t : ℕ =>
          (2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) ^ 2))
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (radius t)
          (utilityGradient voter (center t)) (response t voter))
    {expected realized : ℕ → (ℕ → Voter) → ℝ} {base : ℝ}
    (hcentered :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center i)
              (response i) (sample i)) :
    ∀ᵐ sampledVoter
        ∂theorem3FiniteWeightedVoterSequenceMeasure
          weight hweight_nonneg hweight_sum,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n sampledVoter - fluctuationBound ≤
          base + realized n sampledVoter := by
  let firstIncrement : (ℕ → Voter) → ℝ :=
    fun sample =>
      theorem3FiniteDotCenteredIncrement weight a (center 0)
        (response 0) (sample 0)
  let expectedTail : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => expected (n + 1) sample - firstIncrement sample
  let realizedTail : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => realized (n + 1) sample
  have hcenteredTail :
      ∀ n sample,
        expectedTail n sample - base - realizedTail n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1)) := by
    intro n sample
    let X : ℕ → ℝ :=
      fun i =>
        theorem3FiniteDotCenteredIncrement weight a (center i)
          (response i) (sample i)
    have hfull :
        expected (n + 1) sample - base - realized (n + 1) sample =
          ∑ i ∈ Finset.range (n + 1), X i := by
      simpa [X] using hcentered (n + 1) sample
    have htail :
        (∑ i ∈ Finset.range (n + 1), X i) - X 0 =
          ∑ i ∈ Finset.range n, X (i + 1) :=
      proof_sum_range_succ_sub_first_eq_shifted_tail X n
    calc
      expectedTail n sample - base - realizedTail n sample
          = (expected (n + 1) sample - base - realized (n + 1) sample) -
              firstIncrement sample := by
              ring
      _ = (∑ i ∈ Finset.range (n + 1), X i) - X 0 := by
              rw [hfull]
      _ = ∑ i ∈ Finset.range n, X (i + 1) := htail
      _ = ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1)) := by
              rfl
  have htail_ae :
      ∀ᵐ sampledVoter
          ∂theorem3FiniteWeightedVoterSequenceMeasure
            weight hweight_nonneg hweight_sum,
        ∃ tailFluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
          expectedTail n sampledVoter - tailFluctuationBound ≤
            base + realizedTail n sampledVoter :=
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_radius_shifted
      weight hweight_nonneg hweight_sum a center radius hradius_nonneg
      hradius_sq_summable utilityGradient response hresponse
      (expected := expectedTail) (realized := realizedTail) (base := base)
      hcenteredTail
  filter_upwards [htail_ae] with sampledVoter htail
  rcases htail with ⟨tailFluctuationBound, T, htailBound⟩
  refine ⟨tailFluctuationBound + firstIncrement sampledVoter, T + 1, ?_⟩
  intro n hn
  cases n with
  | zero =>
      omega
  | succ m =>
      have hm : T ≤ m := by omega
      have htail_m := htailBound m hm
      dsimp [expectedTail, realizedTail] at htail_m
      linarith

/--
Existential sampled-voter form of
`proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_ilvRadius_shifted`.
The product measure is a probability measure, so an almost-sure fluctuation
event supplies at least one deterministic sampled voter stream satisfying the
paper's existential shell.
-/
theorem
    proof_theorem3_finiteDot_exists_sampledVoter_of_iid_weightedVoter_modelB_ilvRadius_shifted
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    {expected realized : ℕ → (ℕ → Voter) → ℝ} {base : ℝ}
    (hcentered :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1))) :
    ∃ sampledVoter : ℕ → Voter,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n sampledVoter - fluctuationBound ≤
          base + realized n sampledVoter := by
  let μ : Measure (ℕ → Voter) :=
    theorem3FiniteWeightedVoterSequenceMeasure
      weight hweight_nonneg hweight_sum
  haveI : IsProbabilityMeasure μ :=
    proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
      weight hweight_nonneg hweight_sum
  have hae :
      ∀ᵐ sample ∂μ,
        ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
          expected n sample - fluctuationBound ≤ base + realized n sample := by
    simpa [μ] using
      proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_ilvRadius_shifted
        weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
        hresponse (expected := expected) (realized := realized) (base := base)
        hcentered
  rcases proof_probability_exists_of_ae (μ := μ) hae with
    ⟨sampledVoter, hsampledVoter⟩
  exact ⟨sampledVoter, hsampledVoter⟩

/--
Using the negated finite-dot direction flips the centered selected-voter
increment from selected-minus-expectation to expectation-minus-selected.
-/
theorem proof_theorem3FiniteDotCenteredIncrement_neg_direction_eq_expected_sub_selected
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord]
    (weight : Voter → ℝ)
    (a center : Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (selected : Voter) :
    theorem3FiniteDotCenteredIncrement weight (-a) center response selected =
      (∑ voter : Voter,
        weight voter * finiteDot a (fun i => response voter i - center i)) -
        finiteDot a (fun i => response selected i - center i) := by
  unfold theorem3FiniteDotCenteredIncrement finiteDot
  simp only [Pi.neg_apply, neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring_nf

/--
Unshifted almost-sure sampled-voter concentration for the paper's zero-based
Algorithm 1 indexing.  This is the probability-strengthened form of
`proof_theorem3_finiteDot_exists_sampledVoter_of_iid_weightedVoter_modelB_ilvRadius`.
-/
theorem
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    {expected realized : ℕ → (ℕ → Voter) → ℝ} {base : ℝ}
    (hcentered :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center i)
              (response i) (sample i)) :
    ∀ᵐ sampledVoter
        ∂theorem3FiniteWeightedVoterSequenceMeasure
          weight hweight_nonneg hweight_sum,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n sampledVoter - fluctuationBound ≤
          base + realized n sampledVoter := by
  let firstIncrement : (ℕ → Voter) → ℝ :=
    fun sample =>
      theorem3FiniteDotCenteredIncrement weight a (center 0)
        (response 0) (sample 0)
  let expectedTail : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => expected (n + 1) sample - firstIncrement sample
  let realizedTail : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => realized (n + 1) sample
  have hcenteredTail :
      ∀ n sample,
        expectedTail n sample - base - realizedTail n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1)) := by
    intro n sample
    let X : ℕ → ℝ :=
      fun i =>
        theorem3FiniteDotCenteredIncrement weight a (center i)
          (response i) (sample i)
    have hfull :
        expected (n + 1) sample - base - realized (n + 1) sample =
          ∑ i ∈ Finset.range (n + 1), X i := by
      simpa [X] using hcentered (n + 1) sample
    have htail :
        (∑ i ∈ Finset.range (n + 1), X i) - X 0 =
          ∑ i ∈ Finset.range n, X (i + 1) :=
      proof_sum_range_succ_sub_first_eq_shifted_tail X n
    calc
      expectedTail n sample - base - realizedTail n sample
          = (expected (n + 1) sample - base - realized (n + 1) sample) -
              firstIncrement sample := by
              ring
      _ = (∑ i ∈ Finset.range (n + 1), X i) - X 0 := by
              rw [hfull]
      _ = ∑ i ∈ Finset.range n, X (i + 1) := htail
      _ = ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1)) := by
              rfl
  have htail_ae :
      ∀ᵐ sampledVoter
          ∂theorem3FiniteWeightedVoterSequenceMeasure
            weight hweight_nonneg hweight_sum,
        ∃ tailFluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
          expectedTail n sampledVoter - tailFluctuationBound ≤
            base + realizedTail n sampledVoter :=
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_ilvRadius_shifted
      weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
      hresponse
      (expected := expectedTail) (realized := realizedTail) (base := base)
      hcenteredTail
  filter_upwards [htail_ae] with sampledVoter htail
  rcases htail with ⟨tailFluctuationBound, T, htailBound⟩
  refine ⟨tailFluctuationBound + firstIncrement sampledVoter, T + 1, ?_⟩
  intro n hn
  cases n with
  | zero =>
      omega
  | succ m =>
      have hm : T ≤ m := by omega
      have htail_m := htailBound m hm
      dsimp [expectedTail, realizedTail] at htail_m
      linarith

/--
Unshifted existential sampled-voter concentration for the paper's zero-based
Algorithm 1 indexing.  The martingale theorem controls the tail increments
`1,2,...`; the first centered increment is subtracted in the tail process and
then absorbed into the eventual fluctuation bound.
-/
theorem
    proof_theorem3_finiteDot_exists_sampledVoter_of_iid_weightedVoter_modelB_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    {expected realized : ℕ → (ℕ → Voter) → ℝ} {base : ℝ}
    (hcentered :
      ∀ n sample,
        expected n sample - base - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center i)
              (response i) (sample i)) :
    ∃ sampledVoter : ℕ → Voter,
      ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        expected n sampledVoter - fluctuationBound ≤
          base + realized n sampledVoter := by
  let firstIncrement : (ℕ → Voter) → ℝ :=
    fun sample =>
      theorem3FiniteDotCenteredIncrement weight a (center 0)
        (response 0) (sample 0)
  let expectedTail : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => expected (n + 1) sample - firstIncrement sample
  let realizedTail : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => realized (n + 1) sample
  have hcenteredTail :
      ∀ n sample,
        expectedTail n sample - base - realizedTail n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1)) := by
    intro n sample
    let X : ℕ → ℝ :=
      fun i =>
        theorem3FiniteDotCenteredIncrement weight a (center i)
          (response i) (sample i)
    have hfull :
        expected (n + 1) sample - base - realized (n + 1) sample =
          ∑ i ∈ Finset.range (n + 1), X i := by
      simpa [X] using hcentered (n + 1) sample
    have htail :
        (∑ i ∈ Finset.range (n + 1), X i) - X 0 =
          ∑ i ∈ Finset.range n, X (i + 1) :=
      proof_sum_range_succ_sub_first_eq_shifted_tail X n
    calc
      expectedTail n sample - base - realizedTail n sample
          = (expected (n + 1) sample - base - realized (n + 1) sample) -
              firstIncrement sample := by
              ring
      _ = (∑ i ∈ Finset.range (n + 1), X i) - X 0 := by
              rw [hfull]
      _ = ∑ i ∈ Finset.range n, X (i + 1) := htail
      _ = ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement weight a (center (i + 1))
              (response (i + 1)) (sample (i + 1)) := by
              rfl
  rcases
      proof_theorem3_finiteDot_exists_sampledVoter_of_iid_weightedVoter_modelB_ilvRadius_shifted
        weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
        hresponse
        (expected := expectedTail) (realized := realizedTail) (base := base)
        hcenteredTail with
    ⟨sampledVoter, tailFluctuationBound, T, htailBound⟩
  refine ⟨sampledVoter, tailFluctuationBound + firstIncrement sampledVoter,
    T + 1, ?_⟩
  intro n hn
  cases n with
  | zero =>
      omega
  | succ m =>
      have hm : T ≤ m := by omega
      have htail_m := htailBound m hm
      dsimp [expectedTail, realizedTail] at htail_m
      linarith

/--
Almost-sure iid weighted-voter concentration for the finite-dot projected-trace
shell.  This keeps the product-law probability statement visible before any
deterministic good sampled stream is extracted.
-/
theorem
    proof_theorem3_finiteDot_projectedTrace_concentration_ae_of_iid_weightedVoter
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (hweight_nonneg : ∀ voter, 0 ≤ G.weight voter)
    (hweight_sum : (∑ voter : Voter, G.weight voter) = 1)
    {r0 : ℝ} (hr0 : 0 < r0)
    (xstar : Coord → ℝ) (N : ℕ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
          (ilvRadius r0 (t + 1))
          (G.utilityGradient voter
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
          (response t voter)) :
    ∀ᵐ sampledVoter
        ∂theorem3FiniteWeightedVoterSequenceMeasure
          G.weight hweight_nonneg hweight_sum,
      ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ t ∈ Finset.range n,
            ∑ voter : Voter,
              G.weight voter *
                finiteDot
                  (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                  (fun i =>
                    response t voter i -
                      E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                        (t + N) i)) -
            concentrationBound ≤
          theorem3ConcreteFiniteFieldProjection G xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
            ∑ t ∈ Finset.range n,
              finiteDot
                (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                (fun i =>
                  response t (sampledVoter t) i -
                    E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                      (t + N) i) := by
  classical
  let trajectory : ℕ → Coord → ℝ :=
    fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
  let direction : Coord → ℝ :=
    finiteTheorem3DirectionalField G.weight G.utilityGradient xstar
  let center : ℕ → Coord → ℝ := fun t => trajectory (t + N)
  let expectedTerm : ℕ → ℝ :=
    fun t =>
      ∑ voter : Voter,
        G.weight voter *
          finiteDot direction (fun i => response t voter i - center t i)
  let selectedTerm : ℕ → (ℕ → Voter) → ℝ :=
    fun t sample =>
      finiteDot direction (fun i => response t (sample t) i - center t i)
  let expected : ℕ → (ℕ → Voter) → ℝ :=
    fun n _sample => ∑ t ∈ Finset.range n, expectedTerm t
  let realized : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => ∑ t ∈ Finset.range n, selectedTerm t sample
  have hcentered :
      ∀ n sample,
        expected n sample - (0 : ℝ) - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement G.weight (-direction) (center i)
              (response i) (sample i) := by
    intro n sample
    calc
      expected n sample - (0 : ℝ) - realized n sample
          = (∑ t ∈ Finset.range n, expectedTerm t) -
              ∑ t ∈ Finset.range n, selectedTerm t sample := by
              simp [expected, realized]
      _ = ∑ t ∈ Finset.range n, (expectedTerm t - selectedTerm t sample) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement G.weight (-direction) (center i)
              (response i) (sample i) := by
              apply Finset.sum_congr rfl
              intro t _ht
              exact
                (proof_theorem3FiniteDotCenteredIncrement_neg_direction_eq_expected_sub_selected
                  G.weight direction (center t) (response t) (sample t)).symm
  have hae :
      ∀ᵐ sampledVoter
          ∂theorem3FiniteWeightedVoterSequenceMeasure
            G.weight hweight_nonneg hweight_sum,
        ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
          expected n sampledVoter - fluctuationBound ≤
            (0 : ℝ) + realized n sampledVoter :=
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_ilvRadius
      G.weight hweight_nonneg hweight_sum (-direction) center hr0
      G.utilityGradient response hresponse
      (expected := expected) (realized := realized) (base := 0)
      hcentered
  filter_upwards [hae] with sampledVoter hfluctuation
  rcases hfluctuation with ⟨fluctuationBound, T, hfluctuation⟩
  refine
    ⟨fluctuationBound -
        theorem3ConcreteFiniteFieldProjection G xstar (trajectory N),
      T, ?_⟩
  intro n hn
  have hfluctuation_n := hfluctuation n hn
  dsimp [expected, realized, expectedTerm, selectedTerm, center, direction,
    trajectory] at hfluctuation_n ⊢
  linarith

/--
Concrete iid weighted-voter concentration for the finite-dot projected-trace
shell.  This proves exactly the concentration inequality requested by
`FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics`; the remaining
projected-trace fields are deterministic source/geometry data.
-/
theorem
    proof_theorem3_finiteDot_projectedTrace_concentration_of_iid_weightedVoter
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (hweight_nonneg : ∀ voter, 0 ≤ G.weight voter)
    (hweight_sum : (∑ voter : Voter, G.weight voter) = 1)
    {r0 : ℝ} (hr0 : 0 < r0)
    (xstar : Coord → ℝ) (N : ℕ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
          (ilvRadius r0 (t + 1))
          (G.utilityGradient voter
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
          (response t voter)) :
    ∃ sampledVoter : ℕ → Voter,
      ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ t ∈ Finset.range n,
            ∑ voter : Voter,
              G.weight voter *
                finiteDot
                  (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                  (fun i =>
                    response t voter i -
                      E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                        (t + N) i)) -
            concentrationBound ≤
          theorem3ConcreteFiniteFieldProjection G xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
            ∑ t ∈ Finset.range n,
              finiteDot
                (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                (fun i =>
                  response t (sampledVoter t) i -
                    E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                      (t + N) i) := by
  classical
  let μ : Measure (ℕ → Voter) :=
    theorem3FiniteWeightedVoterSequenceMeasure
      G.weight hweight_nonneg hweight_sum
  haveI : IsProbabilityMeasure μ :=
    proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
      G.weight hweight_nonneg hweight_sum
  have hae :
      ∀ᵐ sampledVoter ∂μ,
        ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
          (∑ t ∈ Finset.range n,
              ∑ voter : Voter,
                G.weight voter *
                  finiteDot
                    (finiteTheorem3DirectionalField G.weight G.utilityGradient
                      xstar)
                    (fun i =>
                      response t voter i -
                        E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                          (t + N) i)) -
              concentrationBound ≤
            theorem3ConcreteFiniteFieldProjection G xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
              ∑ t ∈ Finset.range n,
                finiteDot
                  (finiteTheorem3DirectionalField G.weight G.utilityGradient
                    xstar)
                  (fun i =>
                    response t (sampledVoter t) i -
                      E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                        (t + N) i) := by
    simpa [μ] using
      proof_theorem3_finiteDot_projectedTrace_concentration_ae_of_iid_weightedVoter
        G hweight_nonneg hweight_sum hr0 xstar N response hresponse
  rcases proof_probability_exists_of_ae (μ := μ) hae with
    ⟨sampledVoter, concentrationBound, T, hconcentration⟩
  exact ⟨sampledVoter, concentrationBound, T, hconcentration⟩

/--
Almost-sure iid weighted-voter concentration for the corrected global-radius
projected-trace shell.  The tail beginning at `N` uses the original Algorithm 1
radius `r0 / (t + N + 1)` at tail step `t`.
-/
theorem
    proof_theorem3_finiteDot_projectedTrace_global_concentration_ae_of_iid_weightedVoter
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (hweight_nonneg : ∀ voter, 0 ≤ G.weight voter)
    (hweight_sum : (∑ voter : Voter, G.weight voter) = 1)
    {r0 : ℝ} (hr0 : 0 < r0)
    (xstar : Coord → ℝ) (N : ℕ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
          (ilvTailRadius r0 N t)
          (G.utilityGradient voter
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
          (response t voter)) :
    ∀ᵐ sampledVoter
        ∂theorem3FiniteWeightedVoterSequenceMeasure
          G.weight hweight_nonneg hweight_sum,
      ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ t ∈ Finset.range n,
            ∑ voter : Voter,
              G.weight voter *
                finiteDot
                  (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                  (fun i =>
                    response t voter i -
                      E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                        (t + N) i)) -
            concentrationBound ≤
          theorem3ConcreteFiniteFieldProjection G xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
            ∑ t ∈ Finset.range n,
              finiteDot
                (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                (fun i =>
                  response t (sampledVoter t) i -
                    E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                      (t + N) i) := by
  classical
  let trajectory : ℕ → Coord → ℝ :=
    fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
  let direction : Coord → ℝ :=
    finiteTheorem3DirectionalField G.weight G.utilityGradient xstar
  let center : ℕ → Coord → ℝ := fun t => trajectory (t + N)
  let radius : ℕ → ℝ := fun t => ilvTailRadius r0 N t
  let expectedTerm : ℕ → ℝ :=
    fun t =>
      ∑ voter : Voter,
        G.weight voter *
          finiteDot direction (fun i => response t voter i - center t i)
  let selectedTerm : ℕ → (ℕ → Voter) → ℝ :=
    fun t sample =>
      finiteDot direction (fun i => response t (sample t) i - center t i)
  let expected : ℕ → (ℕ → Voter) → ℝ :=
    fun n _sample => ∑ t ∈ Finset.range n, expectedTerm t
  let realized : ℕ → (ℕ → Voter) → ℝ :=
    fun n sample => ∑ t ∈ Finset.range n, selectedTerm t sample
  have hcentered :
      ∀ n sample,
        expected n sample - (0 : ℝ) - realized n sample =
          ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement G.weight (-direction) (center i)
              (response i) (sample i) := by
    intro n sample
    calc
      expected n sample - (0 : ℝ) - realized n sample
          = (∑ t ∈ Finset.range n, expectedTerm t) -
              ∑ t ∈ Finset.range n, selectedTerm t sample := by
              simp [expected, realized]
      _ = ∑ t ∈ Finset.range n, (expectedTerm t - selectedTerm t sample) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ Finset.range n,
            theorem3FiniteDotCenteredIncrement G.weight (-direction) (center i)
              (response i) (sample i) := by
              apply Finset.sum_congr rfl
              intro t _ht
              exact
                (proof_theorem3FiniteDotCenteredIncrement_neg_direction_eq_expected_sub_selected
                  G.weight direction (center t) (response t) (sample t)).symm
  have hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t := by
    intro t
    exact ilvTailRadius_nonneg (le_of_lt hr0) N t
  have hradius_sq_summable :
      Summable
        (fun t : ℕ =>
          (2 * (finiteCoordinateNorm SourceNorm.l2 (-direction) * radius t)) ^ 2) := by
    have htail := ilvTailRadius_sq_summable r0 N
    have hscaled :
        Summable
          (fun t : ℕ =>
            (2 * finiteCoordinateNorm SourceNorm.l2 (-direction)) ^ 2 *
              (ilvTailRadius r0 N t) ^ 2) :=
      htail.mul_left ((2 * finiteCoordinateNorm SourceNorm.l2 (-direction)) ^ 2)
    refine hscaled.congr ?_
    intro t
    simp [radius]
    ring
  have hae :
      ∀ᵐ sampledVoter
          ∂theorem3FiniteWeightedVoterSequenceMeasure
            G.weight hweight_nonneg hweight_sum,
        ∃ fluctuationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
          expected n sampledVoter - fluctuationBound ≤
            (0 : ℝ) + realized n sampledVoter :=
    proof_theorem3_finiteDot_eventual_fluctuation_of_iid_weightedVoter_modelB_radius
      G.weight hweight_nonneg hweight_sum (-direction) center radius
      hradius_nonneg hradius_sq_summable G.utilityGradient response
      (by
        intro t voter
        simpa [center, radius, trajectory] using hresponse t voter)
      (expected := expected) (realized := realized) (base := 0)
      hcentered
  filter_upwards [hae] with sampledVoter hfluctuation
  rcases hfluctuation with ⟨fluctuationBound, T, hfluctuation⟩
  refine
    ⟨fluctuationBound -
        theorem3ConcreteFiniteFieldProjection G xstar (trajectory N),
      T, ?_⟩
  intro n hn
  have hfluctuation_n := hfluctuation n hn
  dsimp [expected, realized, expectedTerm, selectedTerm, center, direction,
    trajectory] at hfluctuation_n ⊢
  linarith

/--
Construct corrected global-radius pathwise projected-trace semantics from an
almost-sure trace skeleton.  The proof intersects the source trace event with
the iid weighted-voter concentration event for the same product law.
-/
noncomputable def
    proof_theorem3_finiteDotProjectedTraceGlobalPathwiseSemantics_of_iidWeightedVoter_aeTrace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton G) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSemantics G where
  r0 := S.r0
  r0_pos := S.r0_pos
  coordinate_continuity := S.coordinate_continuity
  pathwise_projected_trace := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases S.ae_projected_trace hC hContinuous hResponse hConverges
        hneConcrete hc hdrift with
      ⟨response, hrawResponse, htraceAE⟩
    let μ : Measure (ℕ → Voter) :=
      theorem3FiniteWeightedVoterSequenceMeasure
        G.weight G.weight_nonneg G.weight_sum
    haveI : IsProbabilityMeasure μ :=
      proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
        G.weight G.weight_nonneg G.weight_sum
    have htraceAEμ :
        ∀ᵐ sampledVoter ∂μ,
          ∃ raw : ℕ → Coord → ℝ,
          ∃ project : (Coord → ℝ) → Coord → ℝ,
            UsesFiniteCoordinateNormDistance E ∧
            Convex ℝ E.solutionSpace ∧
            IsNormProjectionOnto E SourceNorm.l2 project ∧
            (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
            (∀ t : ℕ,
              Algorithm1ProjectedUpdate project (raw t)
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (t + 1 + N))) ∧
            (∀ t : ℕ,
              FiniteFeasibleDirectionAt E.solutionSpace
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (t + 1 + N))
                (finiteTheorem3DirectionalField G.weight
                  G.utilityGradient xstar)) := by
      simpa [μ] using htraceAE
    have hconcentrationAEμ :
        ∀ᵐ sampledVoter ∂μ,
          ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
            (∑ t ∈ Finset.range n,
                ∑ voter : Voter,
                  G.weight voter *
                    finiteDot
                      (finiteTheorem3DirectionalField G.weight G.utilityGradient
                        xstar)
                      (fun i =>
                        response t voter i -
                          E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N) i)) -
                concentrationBound ≤
              theorem3ConcreteFiniteFieldProjection G xstar
                (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
                ∑ t ∈ Finset.range n,
                  finiteDot
                    (finiteTheorem3DirectionalField G.weight G.utilityGradient
                      xstar)
                    (fun i =>
                      response t (sampledVoter t) i -
                        E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + N) i) := by
      simpa [μ] using
        proof_theorem3_finiteDot_projectedTrace_global_concentration_ae_of_iid_weightedVoter
          G G.weight_nonneg G.weight_sum S.r0_pos xstar N response hrawResponse
    have hboth := hconcentrationAEμ.and htraceAEμ
    rcases proof_probability_exists_of_ae (μ := μ) hboth with
      ⟨sampledVoter, hconcentration, htrace⟩
    rcases hconcentration with
      ⟨concentrationBound, T, hconcentrationBound⟩
    rcases htrace with
      ⟨raw, project, hNorm, hconv, hproject, hselectedRaw,
        hprojectedUpdate, hfeasibleDirection⟩
    exact
      ⟨⟨sampledVoter,
        { response := response
          raw := raw
          project := project
          normDistance := hNorm
          convex_solutionSpace := hconv
          normProjection := hproject
          raw_response := hrawResponse
          selected_raw := hselectedRaw
          projected_update := hprojectedUpdate
          feasible_direction := hfeasibleDirection
          concentrationBound := concentrationBound
          concentration_time := T
          concentration_control := hconcentrationBound }⟩⟩

/--
The deterministic global trace generator implies the corrected almost-sure trace
skeleton by viewing a pointwise generator as an almost-sure event.
-/
noncomputable def
    proof_theorem3_finiteDotProjectedTraceGlobalAETraceSkeleton_of_deterministicTrace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton G) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton G where
  r0 := S.r0
  r0_pos := S.r0_pos
  coordinate_continuity := S.coordinate_continuity
  ae_projected_trace := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases S.deterministic_projected_trace hC hContinuous hResponse hConverges
        hneConcrete hc hdrift with
      ⟨response, hrawResponse, hdeterministicForSample⟩
    refine ⟨response, hrawResponse, ?_⟩
    refine Filter.Eventually.of_forall ?_
    intro sampledVoter
    rcases hdeterministicForSample sampledVoter with
      ⟨raw, project, hNorm, hproject, hselectedRaw,
        hprojectedUpdate, hfeasibleDirection⟩
    exact
      ⟨raw, project, hNorm, S.convex_solutionSpace hC, hproject,
        hselectedRaw, hprojectedUpdate, hfeasibleDirection⟩

/--
Corrected Theorem 3 endpoint from deterministic projected Algorithm 1 trace
data using the original global tail radii.
-/
theorem proof_theorem3_finite_projectedTraceGlobalDeterministicSkeleton_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTraceGlobalPathwise
      G
      (proof_theorem3_finiteDotProjectedTraceGlobalPathwiseSemantics_of_iidWeightedVoter_aeTrace
        (proof_theorem3_finiteDotProjectedTraceGlobalAETraceSkeleton_of_deterministicTrace
          S))
      hC hContinuous hResponse hConverges

/--
The deterministic, concentration-free source skeleton for the projected-trace
Theorem 3 route.  It supplies the finite `L2` projection trace, raw responses,
convex feasible set, and feasible fixed-field direction; the iid weighted-voter
concentration is added separately by
`proof_theorem3_finiteDotProjectedTraceHoeffdingSemantics_of_iidWeightedVoter_deterministicTrace`.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceDeterministicSkeleton
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField G.weight G.utilityGradient x i -
                finiteTheorem3DirectionalField G.weight G.utilityGradient
                  xstar i| < ε
  convex_solutionSpace :
    ConditionsC123 E → Convex ℝ E.solutionSpace
  deterministic_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField G.weight
                          G.utilityGradient xstar)
                        (finiteTheorem3DirectionalField G.weight
                          G.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (G.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∀ sampledVoter : ℕ → Voter,
                        ∃ raw : ℕ → Coord → ℝ,
                        ∃ project : (Coord → ℝ) → Coord → ℝ,
                          UsesFiniteCoordinateNormDistance E ∧
                          IsNormProjectionOnto E SourceNorm.l2 project ∧
                          (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                          (∀ t : ℕ,
                            Algorithm1ProjectedUpdate project (raw t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))) ∧
                          (∀ t : ℕ,
                            FiniteFeasibleDirectionAt E.solutionSpace
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))
                              (finiteTheorem3DirectionalField G.weight
                                G.utilityGradient xstar))

/--
The universal deterministic skeleton implies the almost-sure trace skeleton by
viewing a pointwise trace generator as an almost-sure trace generator.
-/
noncomputable def
    proof_theorem3_finiteDotProjectedTraceAETraceSkeleton_of_deterministicTrace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceDeterministicSkeleton G) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceAETraceSkeleton G where
  r0 := S.r0
  r0_pos := S.r0_pos
  coordinate_continuity := S.coordinate_continuity
  ae_projected_trace := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases S.deterministic_projected_trace hC hContinuous hResponse hConverges
        hneConcrete hc hdrift with
      ⟨response, hrawResponse, hdeterministicForSample⟩
    refine ⟨response, hrawResponse, ?_⟩
    refine Filter.Eventually.of_forall ?_
    intro sampledVoter
    rcases hdeterministicForSample sampledVoter with
      ⟨raw, project, hNorm, hproject, hselectedRaw,
        hprojectedUpdate, hfeasibleDirection⟩
    exact
      ⟨raw, project, hNorm, S.convex_solutionSpace hC, hproject,
        hselectedRaw, hprojectedUpdate, hfeasibleDirection⟩

/--
Construct pathwise projected-trace semantics from an almost-sure trace skeleton.
The proof intersects the almost-sure selected-trace event with the proved
almost-sure finite-dot concentration event, then extracts one good sampled voter
stream from the probability space.
-/
noncomputable def
    proof_theorem3_finiteDotProjectedTracePathwiseSemantics_of_iidWeightedVoter_aeTrace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceAETraceSkeleton G) :
    FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics G where
  r0 := S.r0
  r0_pos := S.r0_pos
  coordinate_continuity := S.coordinate_continuity
  pathwise_projected_trace := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases S.ae_projected_trace hC hContinuous hResponse hConverges
        hneConcrete hc hdrift with
      ⟨response, hrawResponse, htraceAE⟩
    let μ : Measure (ℕ → Voter) :=
      theorem3FiniteWeightedVoterSequenceMeasure
        G.weight G.weight_nonneg G.weight_sum
    haveI : IsProbabilityMeasure μ :=
      proof_theorem3_finiteWeightedVoterSequenceMeasure_isProbabilityMeasure
        G.weight G.weight_nonneg G.weight_sum
    have htraceAEμ :
        ∀ᵐ sampledVoter ∂μ,
          ∃ raw : ℕ → Coord → ℝ,
          ∃ project : (Coord → ℝ) → Coord → ℝ,
            UsesFiniteCoordinateNormDistance E ∧
            Convex ℝ E.solutionSpace ∧
            IsNormProjectionOnto E SourceNorm.l2 project ∧
            (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
            (∀ t : ℕ,
              Algorithm1ProjectedUpdate project (raw t)
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (t + 1 + N))) ∧
            (∀ t : ℕ,
              FiniteFeasibleDirectionAt E.solutionSpace
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (t + 1 + N))
                (finiteTheorem3DirectionalField G.weight
                  G.utilityGradient xstar)) := by
      simpa [μ] using htraceAE
    have hconcentrationAEμ :
        ∀ᵐ sampledVoter ∂μ,
          ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
            (∑ t ∈ Finset.range n,
                ∑ voter : Voter,
                  G.weight voter *
                    finiteDot
                      (finiteTheorem3DirectionalField G.weight G.utilityGradient
                        xstar)
                      (fun i =>
                        response t voter i -
                          E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N) i)) -
                concentrationBound ≤
              theorem3ConcreteFiniteFieldProjection G xstar
                (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
                ∑ t ∈ Finset.range n,
                  finiteDot
                    (finiteTheorem3DirectionalField G.weight G.utilityGradient
                      xstar)
                    (fun i =>
                      response t (sampledVoter t) i -
                        E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + N) i) := by
      simpa [μ] using
        proof_theorem3_finiteDot_projectedTrace_concentration_ae_of_iid_weightedVoter
          G G.weight_nonneg G.weight_sum S.r0_pos xstar N response hrawResponse
    have hboth := hconcentrationAEμ.and htraceAEμ
    rcases proof_probability_exists_of_ae (μ := μ) hboth with
      ⟨sampledVoter, hconcentration, htrace⟩
    rcases hconcentration with
      ⟨concentrationBound, T, hconcentrationBound⟩
    rcases htrace with
      ⟨raw, project, hNorm, hconv, hproject, hselectedRaw,
        hprojectedUpdate, hfeasibleDirection⟩
    exact
      ⟨⟨sampledVoter,
        { response := response
          raw := raw
          project := project
          normDistance := hNorm
          convex_solutionSpace := hconv
          normProjection := hproject
          raw_response := hrawResponse
          selected_raw := hselectedRaw
          projected_update := hprojectedUpdate
          feasible_direction := hfeasibleDirection
          concentrationBound := concentrationBound
          concentration_time := T
          concentration_control := hconcentrationBound }⟩⟩

/--
Construct the pathwise projected-trace Theorem 3 semantics from deterministic
projected Algorithm 1 trace data plus the proved iid weighted-voter
concentration bridge.

The sampled voter stream chosen by concentration is immediately fed into the
deterministic trace generator, so the selected raw responses, projected updates,
and concentration inequality are attached to the same stream.
-/
noncomputable def
    proof_theorem3_finiteDotProjectedTracePathwiseSemantics_of_iidWeightedVoter_deterministicTrace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceDeterministicSkeleton G) :
    FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics G :=
  proof_theorem3_finiteDotProjectedTracePathwiseSemantics_of_iidWeightedVoter_aeTrace
    (proof_theorem3_finiteDotProjectedTraceAETraceSkeleton_of_deterministicTrace
      S)

/--
Fill the full projected-trace Theorem 3 semantics from deterministic projected
Algorithm 1 trace data plus the proved iid weighted-voter concentration bridge.
-/
noncomputable def
    proof_theorem3_finiteDotProjectedTraceHoeffdingSemantics_of_iidWeightedVoter_deterministicTrace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceDeterministicSkeleton G) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics G :=
  FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics.toProjectedTraceHoeffdingSemantics
    (proof_theorem3_finiteDotProjectedTracePathwiseSemantics_of_iidWeightedVoter_deterministicTrace
      S)

/--
Theorem 3 endpoint from deterministic projected Algorithm 1 trace data.  The
only stochastic ingredient used here is the proved iid weighted-voter
concentration bridge; no SSGM theorem is involved.
-/
theorem proof_theorem3_finite_projectedTraceAETraceSkeleton_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceAETraceSkeleton G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTracePathwise
      G
      (proof_theorem3_finiteDotProjectedTracePathwiseSemantics_of_iidWeightedVoter_aeTrace
        S)
      hC hContinuous hResponse hConverges

/--
Corrected Theorem 3 endpoint from an almost-sure projected Algorithm 1 trace
skeleton using the original global tail radii.  The iid weighted-voter
concentration and the projection residual inequality are proved before this
endpoint is invoked.
-/
theorem proof_theorem3_finite_projectedTraceGlobalAETraceSkeleton_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTraceGlobalPathwise
      G
      (proof_theorem3_finiteDotProjectedTraceGlobalPathwiseSemantics_of_iidWeightedVoter_aeTrace
        S)
      hC hContinuous hResponse hConverges

/--
Corrected Theorem 3 endpoint from the full finite-coordinate source model.  The
source wrapper supplies the concrete finite directional field and global
projected-trace skeleton; concentration is proved by the iid weighted-voter
bridge above.
-/
theorem proof_theorem3_finite_fullConcreteSourceModel_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    proof_theorem3_finite_projectedTraceGlobalDeterministicSkeleton_directionalEquilibrium
      M.theorem3_field
      (finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton_of_traceSource
        M.theorem3_convex M.theorem3_traceSource)
      hC hContinuous hResponse hConverges

/--
Theorem 3 endpoint from deterministic projected Algorithm 1 trace data.  The
universal trace generator is first weakened to an almost-sure trace skeleton,
then combined with the proved iid weighted-voter concentration theorem.
-/
theorem proof_theorem3_finite_projectedTraceDeterministicSkeleton_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceDeterministicSkeleton G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTracePathwise
      G
      (proof_theorem3_finiteDotProjectedTracePathwiseSemantics_of_iidWeightedVoter_deterministicTrace
        S)
      hC hContinuous hResponse hConverges

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_pmfExp_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ)
    (response : Voter → Coord → ℝ) :
    EconCSLib.pmfExp
        (EconCSLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one))
        (fun selected : Voter =>
          finiteDot a (fun i => response selected i - center i) -
            (∑ voter : Voter,
              weight voter *
                finiteDot a (fun i => response voter i - center i))) =
      0 := by
  exact finiteDot_modelB_centered_response_increment_pmfExp_eq_zero
    weight hweight_nonneg hweight_sum a center response

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_pmfExp_eq_zero_sequence
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (t : ℕ) :
    EconCSLib.pmfExp
        (EconCSLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one))
        (fun selected : Voter =>
          finiteDot a (fun i => response t selected i - center t i) -
            (∑ voter : Voter,
              weight voter *
                finiteDot a (fun i => response t voter i - center t i))) =
      0 := by
  exact finiteDot_modelB_centered_response_increment_pmfExp_eq_zero_sequence
    weight hweight_nonneg hweight_sum a center response t

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_integral_toMeasure_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ)
    (response : Voter → Coord → ℝ) :
    ∫ selected : Voter,
        (finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)))
      ∂(EconCSLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one)).toMeasure =
      0 := by
  exact
    finiteDot_modelB_centered_response_increment_integral_toMeasure_eq_zero
      weight hweight_nonneg hweight_sum a center response

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_mem_Icc_and_integral_toMeasure_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter)) :
    (∀ selected : Voter,
      finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)) ∈
        Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))
          (2 * (finiteCoordinateNorm SourceNorm.l2 a * r))) ∧
      ∫ selected : Voter,
          (finiteDot a (fun i => response selected i - center i) -
            (∑ voter : Voter,
              weight voter *
                finiteDot a (fun i => response voter i - center i)))
        ∂(EconCSLib.finiteWeightedPMF weight hweight_nonneg
            (by simpa [hweight_sum] using zero_lt_one)).toMeasure =
        0 := by
  exact
    finiteDot_modelB_centered_response_increment_mem_Icc_and_integral_toMeasure_eq_zero
      weight hweight_nonneg hweight_sum a center hr utilityGradient response
      hresponse

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter)) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun selected : Voter =>
        finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)))
      ((‖(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)) -
          (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))‖₊ / 2) ^ 2)
      (EconCSLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure := by
  exact
    finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure
      weight hweight_nonneg hweight_sum a center hr utilityGradient response
      hresponse

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_sequence
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun selected : Voter =>
        finiteDot a (fun i => response t selected i - center t i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response t voter i - center t i)))
      ((‖(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) -
          (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)))‖₊ / 2) ^ 2)
      (EconCSLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure := by
  exact
    finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_sequence
      weight hweight_nonneg hweight_sum a center radius hradius_nonneg
      utilityGradient response hresponse t

theorem proof_theorem3_finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun selected : Voter =>
        finiteDot a (fun i => response t selected i - center t i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response t voter i - center t i)))
      ((‖(2 * (finiteCoordinateNorm SourceNorm.l2 a *
            ilvRadius r0 (t + 1))) -
          (-(2 * (finiteCoordinateNorm SourceNorm.l2 a *
            ilvRadius r0 (t + 1))))‖₊ / 2) ^ 2)
      (EconCSLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure := by
  exact
    finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_ilvRadius
      weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
      hresponse t

/--
Deterministic residual identity for the finite-dot projection slack: accumulated
selected raw finite-dot movement minus actual scalar projection movement equals
the cumulative selected-response-to-projected-next-iterate residual.
-/
theorem proof_theorem3_finiteDot_selectedRaw_residual_identity
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (xstar : Coord → ℝ) (trajectory : ℕ → Coord → ℝ)
    (sampledVoter : ℕ → Voter) (response : ℕ → Voter → Coord → ℝ)
    (N n : ℕ) :
    theorem3ConcreteFiniteFieldProjection G xstar (trajectory N) +
        ∑ t ∈ Finset.range n,
          finiteDot
            (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
            (fun i => response t (sampledVoter t) i - trajectory (t + N) i) -
        theorem3ConcreteFiniteFieldProjection G xstar (trajectory (n + N)) =
      ∑ t ∈ Finset.range n,
        finiteDot
          (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
          (fun i => response t (sampledVoter t) i -
            trajectory (t + 1 + N) i) := by
  exact theorem3ConcreteFiniteFieldProjection_selectedRaw_residual_identity
    G xstar trajectory sampledVoter response N n

/--
Pointwise nonpositive selected raw residuals give a cumulative residual bound
with bound `0`.
-/
theorem proof_theorem3_finiteDot_selectedRaw_residual_sum_nonpos_of_pointwise
    {Voter Coord : Type*} [Fintype Coord]
    (a : Coord → ℝ) (trajectory : ℕ → Coord → ℝ)
    (sampledVoter : ℕ → Voter) (response : ℕ → Voter → Coord → ℝ)
    (N : ℕ)
    (hresidual :
      ∀ t : ℕ,
        finiteDot a
          (fun i => response t (sampledVoter t) i -
            trajectory (t + 1 + N) i) ≤ 0) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot a
          (fun i => response t (sampledVoter t) i -
            trajectory (t + 1 + N) i) ≤ 0 := by
  exact finiteDot_selectedRaw_residual_sum_nonpos_of_pointwise
    a trajectory sampledVoter response N hresidual

/--
Projection residual is nonpositive in any direction that remains feasible from
the projected point.  This is the geometric condition under which the residual
bound in the projected finite-dot route can be set to zero.
-/
theorem proof_theorem3_finiteDot_projection_residual_nonpos_of_feasible_direction
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next direction : Coord → ℝ}
    (hnormal : FiniteProjectionNormalConeAt X raw next)
    (hfeasible : (fun i => next i + direction i) ∈ X) :
    finiteDot direction (fun i => raw i - next i) ≤ 0 := by
  exact finiteDot_projection_residual_nonpos_of_feasible_direction
    hnormal hfeasible

theorem proof_theorem3_finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next direction : Coord → ℝ}
    (hnormal : FiniteProjectionNormalConeAt X raw next)
    (hfeasible : FiniteFeasibleDirectionAt X next direction) :
    finiteDot direction (fun i => raw i - next i) ≤ 0 := by
  exact finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
    hnormal hfeasible

/--
Cumulative version of
`proof_theorem3_finiteDot_projection_residual_nonpos_of_feasible_direction`.
-/
theorem proof_theorem3_finiteDot_projection_residual_sum_nonpos_of_feasible_direction
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)}
    {raw next : ℕ → Coord → ℝ} {direction : Coord → ℝ}
    (hnormal : ∀ t : ℕ, FiniteProjectionNormalConeAt X (raw t) (next t))
    (hfeasible : ∀ t : ℕ, (fun i => next t i + direction i) ∈ X) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot direction (fun i => raw t i - next t i) ≤ 0 := by
  exact finiteDot_projection_residual_sum_nonpos_of_feasible_direction
    hnormal hfeasible

theorem proof_theorem3_finiteDot_projection_residual_sum_nonpos_of_feasibleDirectionAt
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)}
    {raw next : ℕ → Coord → ℝ} {direction : Coord → ℝ}
    (hnormal : ∀ t : ℕ, FiniteProjectionNormalConeAt X (raw t) (next t))
    (hfeasible : ∀ t : ℕ, FiniteFeasibleDirectionAt X (next t) direction) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot direction (fun i => raw t i - next t i) ≤ 0 := by
  exact finiteDot_projection_residual_sum_nonpos_of_feasibleDirectionAt
    hnormal hfeasible

/--
Residual-bound form of the projected finite-dot route.  The remaining source
work is split into selected-voter concentration and a bound on the cumulative
selected-response-to-projected-next residual.
-/
theorem proof_theorem3_finite_finiteDotProjectedResidualHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedResidualHoeffding
    G D hC hContinuous hResponse hConverges

/--
Residual-bound finite-dot semantics imply the projected finite-dot shell by the
deterministic residual identity.
-/
noncomputable def proof_theorem3_finite_finiteDotProjectedResidual_to_projectedRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics G) :
    FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics G :=
  FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics.toProjectedRawHoeffdingSemantics
    D

/--
Projected-trace finite-dot semantics imply the residual-bound finite-dot shell:
Lean derives the residual bound from finite `L2` norm projection onto a convex
feasible set plus the feasible `G(x*)` direction condition.
-/
noncomputable def proof_theorem3_finite_finiteDotProjectedTrace_to_projectedResidualHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {G : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics G) :
    FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics G :=
  FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics.toProjectedResidualHoeffdingSemantics
    D

/--
Proof-facing Theorem 3 route from selected-voter finite-dot concentration plus
an explicit projected Algorithm 1 trace.  The projection residual is proved
from normal-cone geometry rather than assumed as an opaque slack bound.
-/
theorem proof_theorem3_finite_finiteDotProjectedTraceHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedResidualHoeffding
    G
    (FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics.toProjectedResidualHoeffdingSemantics
      D)
    hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from sampled raw finite-dot concentration plus
projection slack.  This is the current closest projected finite-dot source
target: prove scalar concentration for the selected raw Model B responses and a
bounded slack comparison to the actual projected trajectory.
-/
theorem proof_theorem3_finite_finiteDotProjectedRawHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedRawHoeffding
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from the paper's neighborhood-escape property.
This is closer to Appendix C.6 than the accumulated-projection route: convergence
eventually traps the trajectory in a small `L2` ball, while Model B
drift/concentration says a non-equilibrium limit forces an arbitrarily late exit.
-/
theorem proof_theorem3_finite_neighborhoodEscape_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperNeighborhoodEscapeSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperNeighborhoodEscape
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from coordinate escape.  Lean converts one
arbitrarily late coordinate displacement into finite `L2` neighborhood escape.
-/
theorem proof_theorem3_finite_coordinateEscape_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateEscapeSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateEscape
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from persistent coordinate drift.  Lean supplies
the continuity-to-fixed-coordinate-drift step and then converts coordinate
escape into neighborhood escape; the remaining obligation is the stochastic
coordinate displacement argument.
-/
theorem proof_theorem3_finite_coordinateDriftEscape_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateDriftEscape
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from accumulated signed-coordinate progress.  Lean
uses source-radius divergence to turn the accumulated lower bound into
arbitrarily late coordinate displacement, then into finite `L2` escape.
-/
theorem proof_theorem3_finite_coordinateAccumulation_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateAccumulationSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateAccumulation
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from one-step signed-coordinate progress.  Lean
telescopes the per-step lower bound into accumulated signed-coordinate progress
before applying the coordinate escape route.
-/
theorem proof_theorem3_finite_coordinateStepProgress_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateStepProgressSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateStepProgress
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from the Appendix C.6
expected-drift-minus-fluctuation shell.  Lean absorbs the bounded fluctuation
term into accumulated signed-coordinate progress, then uses the coordinate
escape route.
-/
theorem proof_theorem3_finite_coordinateExpectedFluctuation_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateExpectedFluctuation
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from the C.6 Hoeffding shell.  Lean derives the
expected harmonic coordinate drift from fixed-sign coordinate drift; the
remaining source-side obligation is only the concentration/fluctuation control
for the realized accumulated coordinate motion.
-/
theorem proof_theorem3_finite_coordinateHoeffdingShell_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateHoeffdingShell
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from eventual C.6 Hoeffding control.  This is the
weakest current concentration-facing interface: Lean needs only tail control of
realized accumulated coordinate motion against the expected signed coordinate
sum, then it derives arbitrarily late coordinate escape.
-/
theorem proof_theorem3_finite_coordinateEventualHoeffdingShell_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateEventualHoeffdingShell
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from sampled raw Model B increments.  This exposes
the paper's Appendix C.6 expansion directly: selected raw responses must match
actual coordinate increments, and the remaining concentration claim controls
realized signed increments against their finite-voter expectation.
-/
theorem proof_theorem3_finite_coordinateSampledRawHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateSampledRawHoeffding
    G D hC hContinuous hResponse hConverges

/--
The exact unprojected sampled-raw shell is the zero-projection-slack special
case of the projected sampled-raw shell.  This keeps the projection-sensitive
obligation explicit: actual ILV source semantics should discharge the
projected shell directly, while an unprojected expansion factors through it
with slack `0`.
-/
noncomputable def proof_theorem3_finite_coordinateSampledRaw_to_projectedRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics G) :
    FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics G := by
  exact
    FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics.toProjectedRawHoeffdingSemantics
      D

/--
Proof-facing finite-dot expectation identity for raw Model B responses.  This
lifts the coordinate Appendix C.6 expectation calculation to the scalar
projection used by the projected-progress route.
-/
theorem proof_theorem3_finiteDot_expected_modelB_response_increment
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    {x : Coord → ℝ} {response : Voter → Coord → ℝ}
    (a : Coord → ℝ) (r : ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 x r
          (utilityGradient voter x) (response voter)) :
    (∑ voter : Voter,
      weight voter * finiteDot a (fun i => response voter i - x i)) =
      r * finiteDot a
        (finiteTheorem3DirectionalField weight utilityGradient x) := by
  exact
    finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment
      weight utilityGradient a r hresponse

/--
Finite accumulated version of
`proof_theorem3_finiteDot_expected_modelB_response_increment`.
-/
theorem proof_theorem3_finiteDot_expected_modelB_response_increment_sum
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (a : Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter)) :
    ∀ n : ℕ,
      (∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          weight voter *
            finiteDot a (fun i => response t voter i - center t i)) =
        ∑ t ∈ Finset.range n,
          radius t *
            finiteDot a
              (finiteTheorem3DirectionalField weight utilityGradient
                (center t)) := by
  exact
    finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment_sum
      weight utilityGradient center radius response a hresponse

/--
Proof-facing Theorem 3 route from sampled raw Model B increments with explicit
projection slack.  This is the projected analogue of the paper's unprojected
C.6 expansion: concentration controls sampled raw increments, and a separate
slack bound accounts for projection's effect on the drift coordinate.
-/
theorem proof_theorem3_finite_coordinateProjectedRawHoeffding_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateProjectedRawHoeffding
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from concrete paper-radius projected escape with
explicit finite-coordinate convergence.  This is the intended post-concentration
boundary for the paper's stochastic Model B proof: Lean derives convergence of
the scalar field projection and then contradicts accumulated projected escape.
-/
theorem proof_theorem3_finite_paperRadiusEscape_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperRadiusEscapeSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEscape
    G D hC hContinuous hResponse hConverges

/--
Proof-facing Theorem 3 route from one-step paper-radius projected progress with
explicit finite-coordinate convergence.  This stronger deterministic interface
telescopes into the primary paper-radius escape boundary.
-/
theorem proof_theorem3_finite_paperRadiusProgress_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperRadiusProgressSemantics G)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusProgress
    G D hC hContinuous hResponse hConverges

/--
Historical finite-coordinate comparison interface for the generic
`SSGMConvergenceBoundary` marker.  The current public route uses the
theorem-shaped premise `assumption_ssgm_convergence_theorem`; this record remains
only as proof-facing scaffolding showing how the older marker-based obligations
factor through finite-coordinate source data. Theorem 3 is not an SSGM boundary
field here: it is discharged by the environment's deterministic Model B drift
semantics.
-/
structure FiniteCoordinateILVBoundaryInterfaces
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem1_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Theorem1SSGMConvergenceTheorem E)
  theorem2_source : Theorem2SourceToFiniteSSGMBridge E
  theorem2_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Theorem2SSGMConvergenceTheorem E)
  proposition1_source : Proposition1SourceToFiniteSSGMBridge E
  proposition1_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Proposition1SSGMConvergenceTheorem E)
  proposition2_source : Proposition2SourceToSSGMBridge E
  proposition2_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Proposition2SSGMConvergenceTheorem E)

theorem proof_ilvSSGMConvergenceConsequences_of_finiteBoundaryInterfaces
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (B : FiniteCoordinateILVBoundaryInterfaces E) :
    ILVSSGMConvergenceConsequences E := by
  refine
    { theorem1_consequence := ?_
      theorem2_consequence := ?_
      proposition1_consequence := ?_
      proposition2_consequence := ?_ }
  · exact proof_theorem1Statement_of_ssgmBoundary B.theorem1_boundary
  · exact proof_theorem2Statement_of_sourceBridge_ssgmBoundary
      B.theorem2_source B.theorem2_boundary
  · exact proof_proposition1Statement_of_sourceBridge_ssgmBoundary
      B.proposition1_source B.proposition1_boundary
  · exact proof_proposition2Statement_of_sourceBridge_ssgmBoundary
      B.proposition2_source B.proposition2_boundary

/--
Strict finite-coordinate source-interface bundle for the non-SSGM parts of the
paper proof.  These are deterministic/source-semantics obligations: they should
be proved from a stronger concrete interpretation of C1-C3 and the Model A/B
response predicates, not hidden inside the stochastic subgradient convergence
boundary.
-/
structure FiniteCoordinateILVSourceInterfaces
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem2_source : Theorem2SourceToFiniteSSGMBridge E
  proposition1_source : Proposition1SourceToFiniteSSGMBridge E
  proposition2_source : Proposition2SourceToSSGMBridge E

noncomputable def proof_finiteCoordinateILVSourceInterfaces_of_semantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (T2 : Theorem2SourceSemantics E)
    (P1 : Proposition1SourceSemantics E)
    (P2 : Proposition2SourceSemantics E) :
    FiniteCoordinateILVSourceInterfaces E where
  theorem2_source := theorem2SourceToFiniteSSGMBridge_of_semantics T2
  proposition1_source := proposition1SourceToFiniteSSGMBridge_of_semantics P1
  proposition2_source := proposition2SourceToSSGMBridge_of_semantics P2

/--
Strict finite-coordinate SSGM-only boundary bundle.  Unlike
`FiniteCoordinateILVBoundaryInterfaces`, this record contains only stochastic
subgradient convergence theorem boundaries; Theorem 3 is not included because
its paper statement is post-convergence deterministic.  This is a legacy
proof-facing adapter for the old marker-based development, not a public paper
assumption surface; the public GKGMM closeout uses the single theorem-shaped
declaration `assumption_ssgm_convergence_theorem`.
-/
structure FiniteCoordinateILVSSGMBoundaries
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem1_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Theorem1SSGMConvergenceTheorem E)
  theorem2_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Theorem2SSGMConvergenceTheorem E)
  proposition1_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Proposition1SSGMConvergenceTheorem E)
  proposition2_boundary :
    EconCSLib.Optimization.SSGMConvergenceBoundary
      (Proposition2SSGMConvergenceTheorem E)

/--
Strict replacement for the broad endpoint boundary in finite-coordinate
environments: deterministic source interfaces plus SSGM-only convergence
boundaries imply the four stochastic convergence endpoint consequences.
-/
theorem proof_ilvSSGMConvergenceConsequences_of_strictFiniteInterfaces
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVSourceInterfaces E)
    (B : FiniteCoordinateILVSSGMBoundaries E) :
    ILVSSGMConvergenceConsequences E := by
  refine
    { theorem1_consequence := ?_
      theorem2_consequence := ?_
      proposition1_consequence := ?_
      proposition2_consequence := ?_ }
  · exact proof_theorem1Statement_of_ssgmBoundary B.theorem1_boundary
  · exact proof_theorem2Statement_of_sourceBridge_ssgmBoundary
      S.theorem2_source B.theorem2_boundary
  · exact proof_proposition1Statement_of_sourceBridge_ssgmBoundary
      S.proposition1_source B.proposition1_boundary
  · exact proof_proposition2Statement_of_sourceBridge_ssgmBoundary
      S.proposition2_source B.proposition2_boundary

theorem proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmBoundaries
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (T2 : Theorem2SourceSemantics E)
    (P1 : Proposition1SourceSemantics E)
    (P2 : Proposition2SourceSemantics E)
    (B : FiniteCoordinateILVSSGMBoundaries E) :
    ILVSSGMConvergenceConsequences E := by
  refine
    { theorem1_consequence := ?_
      theorem2_consequence := ?_
      proposition1_consequence := ?_
      proposition2_consequence := ?_ }
  · exact proof_theorem1Statement_of_ssgmBoundary B.theorem1_boundary
  · exact proof_theorem2Statement_of_sourceSemantics_ssgmBoundary
      T2 B.theorem2_boundary
  · exact proof_proposition1Statement_of_sourceSemantics_ssgmBoundary
      P1 B.proposition1_boundary
  · exact proof_proposition2Statement_of_sourceSemantics_ssgmBoundary
      P2 B.proposition2_boundary

theorem proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (T2 : Theorem2SourceSemantics E)
    (P1 : Proposition1SourceSemantics E)
    (P2 : Proposition2SourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  exact
    ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
      T2 P1 P2 S

noncomputable def proof_finiteCoordinateILVSourceInterfaces_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    FiniteCoordinateILVSourceInterfaces E :=
  proof_finiteCoordinateILVSourceInterfaces_of_semantics
    (theorem2SourceSemantics_of_concreteSourceModel M)
    (proposition1SourceSemantics_of_concreteSourceModel M)
    (proposition2SourceSemantics_of_concreteSourceModel M)

def proof_theorem2SourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Theorem2SourceSemantics E :=
  theorem2SourceSemantics_of_concreteSourceModel M

def proof_theorem2PrimitiveSourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Theorem2PrimitiveSourceSemantics E :=
  theorem2PrimitiveSourceSemantics_of_concreteSourceModel M

def proof_proposition1SourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Proposition1SourceSemantics E :=
  proposition1SourceSemantics_of_concreteSourceModel M

noncomputable def proof_proposition2SourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Proposition2SourceSemantics E :=
  proposition2SourceSemantics_of_concreteSourceModel M

theorem proof_ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmBoundaries
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (B : FiniteCoordinateILVSSGMBoundaries E) :
    ILVSSGMConvergenceConsequences E := by
  refine
    { theorem1_consequence := ?_
      theorem2_consequence := ?_
      proposition1_consequence := ?_
      proposition2_consequence := ?_ }
  · exact proof_theorem1Statement_of_ssgmBoundary B.theorem1_boundary
  · exact proof_theorem2Statement_of_concreteSourceModel_ssgmBoundary
      M B.theorem2_boundary
  · exact proof_proposition1Statement_of_concreteSourceModel_ssgmBoundary
      M B.proposition1_boundary
  · exact proof_proposition2Statement_of_concreteSourceModel_ssgmBoundary
      M B.proposition2_boundary

/--
Current theorem-shaped finite-coordinate handoff: concrete deterministic source
semantics plus the SSGM convergence theorem bundle imply the four convergence
endpoint consequences.
-/
theorem proof_ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  exact ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    M S

theorem proof_ilvSSGMConvergenceConsequences_of_fullConcreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  exact ilvSSGMConvergenceConsequences_of_fullConcreteSourceModel_ssgmConvergence
    M S

/--
Granular full finite-coordinate source semantics for the paper, excluding only
the reusable SSGM convergence theorem.  Compared with
`FiniteCoordinateILVFullConcreteSourceModel`, the SSGM-backed rows are supplied
as theorem-specific source semantics, so the Theorem 2, Proposition 1, and
Proposition 2 deterministic obligations remain separately auditable.
-/
structure FiniteCoordinateILVFullSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem2_source : Theorem2SourceSemantics E
  proposition1_source : Proposition1SourceSemantics E
  proposition2_source : Proposition2SourceSemantics E
  theorem3_field : FiniteTheorem3DirectionalFieldModel E
  theorem3_convex_solutionSpace :
    C1ConvexSolutionSpaceSource E
  theorem3_convergence :
    FiniteCoordinateConvergenceSource E
  theorem3_continuity :
    FiniteTheorem3ConcreteFieldContinuitySource theorem3_field
  theorem3_trace :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
      theorem3_field

def FiniteCoordinateILVFullSourceSemantics.theorem3_traceSource
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSourceSemantics E) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
      S.theorem3_field :=
  finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource_of_core
    S.theorem3_continuity S.theorem3_trace

theorem FiniteCoordinateILVFullSourceSemantics.theorem3_convex
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSourceSemantics E) :
    ConditionsC123 E → Convex ℝ E.solutionSpace :=
  fun _ => S.theorem3_convex_solutionSpace.convex_solutionSpace

def FiniteCoordinateILVFullSourceSemantics.theorem3_deterministicSkeleton
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSourceSemantics E) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
      S.theorem3_field :=
  finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton_of_traceSource
    S.theorem3_convex S.theorem3_traceSource

theorem proof_theorem3_finite_fullSourceSemantics_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSourceSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    proof_theorem3_finite_projectedTraceGlobalDeterministicSkeleton_directionalEquilibrium
      S.theorem3_field S.theorem3_deterministicSkeleton
      hC hContinuous hResponse hConverges

noncomputable def proof_finiteCoordinateILVFullSourceSemantics_of_fullConcreteSourceModel
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E) :
    FiniteCoordinateILVFullSourceSemantics E where
  theorem2_source :=
    theorem2SourceSemantics_of_concreteSourceModel M.convergence_source
  proposition1_source :=
    proposition1SourceSemantics_of_concreteSourceModel M.convergence_source
  proposition2_source :=
    proposition2SourceSemantics_of_concreteSourceModel M.convergence_source
  theorem3_field := M.theorem3_field
  theorem3_convex_solutionSpace := M.theorem3_convex_solutionSpace
  theorem3_convergence := M.theorem3_convergence
  theorem3_continuity := M.theorem3_continuity
  theorem3_trace := M.theorem3_trace

/--
Full finite-coordinate closeout bundle for the named paper results.  The first
four fields are exactly the SSGM-backed convergence statements.  The final two
fields record the non-SSGM Theorem 3 work: the concrete finite directional field
implies the paper's displayed directional-field formula, and the corrected
global-radius projected trace route proves the directional-equilibrium
conclusion for every finite-coordinate convergent Model B `L2` trajectory.
-/
structure FiniteCoordinateILVFullPaperConsequences
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop where
  theorem1_consequence : theorem1Statement E
  theorem2_consequence : theorem2Statement E
  proposition1_consequence : proposition1Statement E
  proposition2_consequence : proposition2Statement E
  theorem3_field_formula : Theorem3DirectionalFieldFormula E
  theorem3_consequence :
    ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          ∀ xstar,
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              IsDirectionalEquilibrium E xstar
  theorem3_statement_consequence : theorem3Statement E

/--
Concrete full source semantics plus the single SSGM convergence theorem bundle
prove all finite-coordinate named paper endpoints represented in Lean.
-/
theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullConcreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  let C :=
    proof_ilvSSGMConvergenceConsequences_of_fullConcreteSourceModel_ssgmConvergence
      M S
  refine
    { theorem1_consequence := C.theorem1_consequence
      theorem2_consequence := C.theorem2_consequence
      proposition1_consequence := C.proposition1_consequence
      proposition2_consequence := C.proposition2_consequence
      theorem3_field_formula :=
        theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel
          M.theorem3_field
      theorem3_consequence := ?_
      theorem3_statement_consequence := ?_ }
  · intro hC hContinuous hResponse xstar hConverges
    exact
      proof_theorem3_finite_fullConcreteSourceModel_directionalEquilibrium
        M hC hContinuous hResponse hConverges
  · intro _hG hC hContinuous hResponse xstar hConverges
    exact
      proof_theorem3_finite_fullConcreteSourceModel_directionalEquilibrium
        M hC hContinuous hResponse
        (M.theorem3_convergence.finite_coordinate_of_ilv_converges hConverges)

/--
Granular full source semantics plus the single SSGM convergence theorem bundle
prove all finite-coordinate named paper endpoints represented in Lean.
-/
theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullSourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  let C :=
    proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
      M.theorem2_source M.proposition1_source M.proposition2_source S
  refine
    { theorem1_consequence := C.theorem1_consequence
      theorem2_consequence := C.theorem2_consequence
      proposition1_consequence := C.proposition1_consequence
      proposition2_consequence := C.proposition2_consequence
      theorem3_field_formula :=
        theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel
          M.theorem3_field
      theorem3_consequence := ?_
      theorem3_statement_consequence := ?_ }
  · intro hC hContinuous hResponse xstar hConverges
    exact
      proof_theorem3_finite_fullSourceSemantics_directionalEquilibrium
        M hC hContinuous hResponse hConverges
  · intro _hG hC hContinuous hResponse xstar hConverges
    exact
      proof_theorem3_finite_fullSourceSemantics_directionalEquilibrium
        M hC hContinuous hResponse
        (M.theorem3_convergence.finite_coordinate_of_ilv_converges hConverges)

/--
Current finite-coordinate paper closeout using the approved single theorem-shaped
SSGM boundary premise.  No Lean axiom is used; the non-SSGM source semantics are the
visible fields of `FiniteCoordinateILVFullConcreteSourceModel`.
-/
theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullConcreteSourceModel
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  exact
    proof_finiteCoordinateILVFullPaperConsequences_of_fullConcreteSourceModel_ssgmConvergence
      M hSSGM

/--
Granular finite-coordinate paper closeout using the approved single
theorem-shaped SSGM boundary premise.  No Lean axiom is used; all non-SSGM source
semantics are visible in theorem-specific and Theorem 3 fields.
-/
theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  exact
    proof_finiteCoordinateILVFullPaperConsequences_of_fullSourceSemantics_ssgmConvergence
      M hSSGM

/--
Granular full source semantics with the refined Theorem 2 primitive trace
source.  This variant keeps Theorem 2's coordinate-noncollision trace primitive
visible and derives the older bad-event trace source only through
`theorem2SourceSemantics_of_primitive`.  It also keeps Theorem 3's projected
Algorithm 1 update source and aggregate feasible-direction source primitive,
deriving the deterministic trace-core source through
`finiteTheorem3GlobalProjectedAlgorithm1TraceSource_of_update_aggregateFeasibility`
and
`finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource_of_algorithm1Trace`.
-/
structure FiniteCoordinateILVFullPrimitiveSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem2_source : Theorem2PrimitiveSourceSemantics E
  proposition1_source : Proposition1ConcreteComponentSourceSemantics E
  proposition2_source : Proposition2SourceSemantics E
  theorem3_field : FiniteTheorem3DirectionalFieldModel E
  theorem3_convex_solutionSpace :
    C1ConvexSolutionSpaceSource E
  theorem3_convergence :
    FiniteCoordinateConvergenceSource E
  theorem3_continuity :
    FiniteTheorem3ConcreteFieldContinuitySource theorem3_field
  theorem3_algorithm1_trace :
    FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource theorem3_field
  theorem3_aggregate_feasibility :
    FiniteTheorem3GlobalProjectedAggregateFeasibilitySource theorem3_field

noncomputable def FiniteCoordinateILVFullPrimitiveSourceSemantics.toFullSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullPrimitiveSourceSemantics E) :
    FiniteCoordinateILVFullSourceSemantics E where
  theorem2_source := theorem2SourceSemantics_of_primitive S.theorem2_source
  proposition1_source :=
    proposition1SourceSemantics_of_componentSemantics
      (proposition1ComponentSourceSemantics_of_concreteComponentSemantics
        S.proposition1_source)
  proposition2_source := S.proposition2_source
  theorem3_field := S.theorem3_field
  theorem3_convex_solutionSpace := S.theorem3_convex_solutionSpace
  theorem3_convergence := S.theorem3_convergence
  theorem3_continuity := S.theorem3_continuity
  theorem3_trace :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource_of_algorithm1Trace
      (finiteTheorem3GlobalProjectedAlgorithm1TraceSource_of_update_aggregateFeasibility
        S.theorem3_algorithm1_trace S.theorem3_aggregate_feasibility)

/--
Granular full source semantics with sampled-process Theorem 2 and Proposition 1
sources.  The sampled records derive the deterministic noncollision fields used
by the older SSGM bridges from marginal-law/bad-event arguments, leaving the
SSGM convergence theorem as the only external theorem boundary for the named
convergence endpoints.
-/
structure FiniteCoordinateILVFullSampledSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem2_source : Theorem2SampledSourceSemantics E
  proposition1_source : Proposition1ConcreteComponentSampledSourceSemantics E
  proposition2_source : Proposition2SourceSemantics E
  theorem3_field : FiniteTheorem3DirectionalFieldModel E
  theorem3_convex_solutionSpace :
    C1ConvexSolutionSpaceSource E
  theorem3_convergence :
    FiniteCoordinateConvergenceSource E
  theorem3_continuity :
    FiniteTheorem3ConcreteFieldContinuitySource theorem3_field
  theorem3_algorithm1_trace :
    FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource theorem3_field
  theorem3_aggregate_feasibility :
    FiniteTheorem3GlobalProjectedAggregateFeasibilitySource theorem3_field

noncomputable def
    FiniteCoordinateILVFullSampledSourceSemantics.toPrimitiveSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledSourceSemantics E) :
    FiniteCoordinateILVFullPrimitiveSourceSemantics E where
  theorem2_source :=
    proof_theorem2PrimitiveSourceSemantics_of_sampledSourceSemantics
      S.theorem2_source
  proposition1_source :=
    proof_proposition1ConcreteComponentSourceSemantics_of_sampledSourceSemantics
      S.proposition1_source
  proposition2_source := S.proposition2_source
  theorem3_field := S.theorem3_field
  theorem3_convex_solutionSpace := S.theorem3_convex_solutionSpace
  theorem3_convergence := S.theorem3_convergence
  theorem3_continuity := S.theorem3_continuity
  theorem3_algorithm1_trace := S.theorem3_algorithm1_trace
  theorem3_aggregate_feasibility := S.theorem3_aggregate_feasibility

noncomputable def FiniteCoordinateILVFullSampledSourceSemantics.toFullSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledSourceSemantics E) :
    FiniteCoordinateILVFullSourceSemantics E :=
  S.toPrimitiveSourceSemantics.toFullSourceSemantics

/--
Sampled full source semantics for the no-hidden-premise closeout.  It keeps all
SSGM-backed theorem source data and the projected Algorithm 1 update source for
Theorem 3, but deliberately does not include the aggregate feasible-direction
source.  The resulting Theorem 3 endpoint is the constrained alternative, plus
exact recovery under `E.solutionSpace = Set.univ`.
-/
structure FiniteCoordinateILVFullSampledProjectedSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  theorem2_source : Theorem2SampledSourceSemantics E
  proposition1_source : Proposition1ConcreteComponentSampledSourceSemantics E
  proposition2_source : Proposition2SourceSemantics E
  theorem3_field : FiniteTheorem3DirectionalFieldModel E
  theorem3_convex_solutionSpace :
    C1ConvexSolutionSpaceSource E
  theorem3_convergence :
    FiniteCoordinateConvergenceSource E
  theorem3_continuity :
    FiniteTheorem3ConcreteFieldContinuitySource theorem3_field
  theorem3_algorithm1_update :
    FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource theorem3_field

noncomputable def
    FiniteCoordinateILVFullSampledProjectedSourceSemantics.theorem2SourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledProjectedSourceSemantics E) :
    Theorem2SourceSemantics E :=
  proof_theorem2SourceSemantics_of_sampledSourceSemantics S.theorem2_source

noncomputable def
    FiniteCoordinateILVFullSampledProjectedSourceSemantics.proposition1SourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledProjectedSourceSemantics E) :
    Proposition1SourceSemantics E :=
  proof_proposition1SourceSemantics_of_sampledConcreteComponentSourceSemantics
    S.proposition1_source

theorem proof_theorem3_finite_fullPrimitiveSourceSemantics_directionalEquilibrium
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullPrimitiveSourceSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    proof_theorem3_finite_fullSourceSemantics_directionalEquilibrium
      S.toFullSourceSemantics hC hContinuous hResponse hConverges

/-- Proof-interface wrapper: in full finite-coordinate space every direction is feasible. -/
theorem proof_finiteFeasibleDirectionAt_univ
    {Coord : Type*} [Fintype Coord]
    (point direction : Coord → ℝ) :
    FiniteFeasibleDirectionAt (Set.univ : Set (Coord → ℝ))
      point direction := by
  exact finiteFeasibleDirectionAt_univ point direction

/--
Proof-interface wrapper for the full-space recovery of Theorem 3's aggregate
feasibility source.  This is the explicit replacement for reading the paper's
unprojected drift expansion as if projection had no boundary effect.
-/
def proof_theorem3_aggregateFeasibilitySource_of_univ_solutionSpace
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ))) :
    FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M :=
  finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_univ_solutionSpace
    hUniv

/--
Corrected projected Theorem 3 alternative.  From projected Algorithm 1 update
semantics, field continuity, convexity, and convergence alone, a nonzero
limiting aggregate field is incompatible with an aggregate feasible-direction
certificate.  Equivalently, the original `G(x*) = 0` conclusion needs that
geometric certificate; otherwise the remaining outcome is a projected boundary
obstruction.
-/
theorem
    proof_theorem3_finite_no_aggregateFeasibilitySource_of_nonzero_convergent_projectedUpdate
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (C : FiniteTheorem3ConcreteFieldContinuitySource M)
    (U : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M)
    (hConvex : ConditionsC123 E → Convex ℝ E.solutionSpace)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar)
    (hNonzero :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) :
    ¬ FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M := by
  intro F
  let traceSource :
      FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M :=
    finiteTheorem3GlobalProjectedAlgorithm1TraceSource_of_update_aggregateFeasibility
      U F
  let core :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
        M :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource_of_algorithm1Trace
      traceSource
  let trace :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
        M :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource_of_core
      C core
  let skeleton :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
        M :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton_of_traceSource
      hConvex trace
  have hEq :
      IsDirectionalEquilibrium E xstar :=
    proof_theorem3_finite_projectedTraceGlobalDeterministicSkeleton_directionalEquilibrium
      M skeleton hC hContinuous hResponse hConverges
  have hEq' : E.directionalField xstar = E.zeroDirection := by
    simpa [IsDirectionalEquilibrium] using hEq
  apply hNonzero
  calc
    finiteTheorem3DirectionalField M.weight M.utilityGradient xstar =
        E.directionalField xstar := by
          symm
          rw [M.directionalField_eq]
    _ = E.zeroDirection := hEq'
    _ = (fun _ => (0 : ℝ)) := by
          symm
          rw [M.zeroDirection_eq]

/--
Constrained/projected conclusion for Theorem 3 without assuming aggregate
feasibility: either the paper's original zero-field conclusion holds, or the
aggregate feasible-direction source cannot be supplied.  This is the audited
boundary alternative exposed by the projection residual argument.
-/
theorem
    proof_theorem3_finite_zero_or_no_aggregateFeasibilitySource_of_convergent_projectedUpdate
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (C : FiniteTheorem3ConcreteFieldContinuitySource M)
    (U : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M)
    (hConvex : ConditionsC123 E → Convex ℝ E.solutionSpace)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar =
        fun _ => (0 : ℝ)) ∨
      ¬ FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M := by
  by_cases hzero :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar =
        fun _ => (0 : ℝ)
  · exact Or.inl hzero
  · exact Or.inr
      (proof_theorem3_finite_no_aggregateFeasibilitySource_of_nonzero_convergent_projectedUpdate
        M C U hConvex hC hContinuous hResponse hConverges hzero)

/--
Record-free constrained/projected conclusion for Theorem 3.  This is the
strongest no-hidden-premise general statement currently derivable from projected
updates and convergence: either the paper's zero-field conclusion holds, or the
aggregate feasible-direction formula is false.
-/
theorem
    proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (C : FiniteTheorem3ConcreteFieldContinuitySource M)
    (U : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M)
    (hConvex : ConditionsC123 E → Convex ℝ E.solutionSpace)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar =
        fun _ => (0 : ℝ)) ∨
      ¬ FiniteTheorem3AggregateFeasibleDirectionFormula M := by
  rcases
      proof_theorem3_finite_zero_or_no_aggregateFeasibilitySource_of_convergent_projectedUpdate
        M C U hConvex hC hContinuous hResponse hConverges with
    hzero | hnoSource
  · exact Or.inl hzero
  · exact Or.inr fun hformula =>
      hnoSource
        (finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_formula
          hformula)

theorem
    proof_theorem3_finite_fullSampledProjectedSourceSemantics_zero_or_no_aggregateFeasibleDirectionFormula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    (finiteTheorem3DirectionalField S.theorem3_field.weight
        S.theorem3_field.utilityGradient xstar =
        fun _ => (0 : ℝ)) ∨
      ¬ FiniteTheorem3AggregateFeasibleDirectionFormula S.theorem3_field := by
  exact
    proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate
      S.theorem3_field S.theorem3_continuity S.theorem3_algorithm1_update
      (fun _ => S.theorem3_convex_solutionSpace.convex_solutionSpace)
      hC hContinuous hResponse hConverges

/--
Full-space recovery theorem.  If projected Algorithm 1 update semantics are
available and the solution space is all finite-coordinate space, the aggregate
feasible-direction certificate is proved directly, so the original Theorem 3
zero-field/directional-equilibrium endpoint follows.
-/
theorem
    proof_theorem3_finite_directionalEquilibrium_of_convergent_projectedUpdate_univ_solutionSpace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (C : FiniteTheorem3ConcreteFieldContinuitySource M)
    (U : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M)
    (hConvex : ConditionsC123 E → Convex ℝ E.solutionSpace)
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  let F : FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M :=
    finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_univ_solutionSpace
      hUniv
  let traceSource :
      FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M :=
    finiteTheorem3GlobalProjectedAlgorithm1TraceSource_of_update_aggregateFeasibility
      U F
  let core :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
        M :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource_of_algorithm1Trace
      traceSource
  let trace :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
        M :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource_of_core
      C core
  let skeleton :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
        M :=
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton_of_traceSource
      hConvex trace
  exact
    proof_theorem3_finite_projectedTraceGlobalDeterministicSkeleton_directionalEquilibrium
      M skeleton hC hContinuous hResponse hConverges

theorem
    proof_theorem3_finite_fullSampledProjectedSourceSemantics_directionalEquilibrium_univ_solutionSpace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    proof_theorem3_finite_directionalEquilibrium_of_convergent_projectedUpdate_univ_solutionSpace
      S.theorem3_field S.theorem3_continuity S.theorem3_algorithm1_update
      (fun _ => S.theorem3_convex_solutionSpace.convex_solutionSpace)
      hUniv hC hContinuous hResponse hConverges

theorem proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ))) :
    theorem3Statement E := by
  intro _hG hC hContinuous hResponse xstar hConverges
  exact
    proof_theorem3_finite_fullSampledProjectedSourceSemantics_directionalEquilibrium_univ_solutionSpace
      S hUniv hC hContinuous hResponse
      (S.theorem3_convergence.finite_coordinate_of_ilv_converges hConverges)

/--
No-hidden-premise finite-coordinate closeout.  The first four fields are the
SSGM-backed named convergence statements.  The Theorem 3 fields state exactly
what the projected proof currently establishes without assuming aggregate
feasibility: the constrained alternative in general, and the paper's exact
Theorem 3 statement in full finite-coordinate space.
-/
structure FiniteCoordinateILVFullProjectedPaperConsequences
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : FiniteCoordinateILVFullSampledProjectedSourceSemantics E) : Prop where
  theorem1_consequence : theorem1Statement E
  theorem2_consequence : theorem2Statement E
  proposition1_consequence : proposition1Statement E
  proposition2_consequence : proposition2Statement E
  theorem3_field_formula : Theorem3DirectionalFieldFormula E
  theorem3_constrained_alternative :
    ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          ∀ xstar,
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField S.theorem3_field.weight
                  S.theorem3_field.utilityGradient xstar =
                  fun _ => (0 : ℝ)) ∨
                ¬ FiniteTheorem3AggregateFeasibleDirectionFormula
                  S.theorem3_field
  theorem3_fullSpace_statement :
    E.solutionSpace = (Set.univ : Set (Coord → ℝ)) →
      theorem3Statement E

theorem
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullProjectedPaperConsequences M := by
  let C :=
    proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
      M.theorem2SourceSemantics M.proposition1SourceSemantics
      M.proposition2_source S
  refine
    { theorem1_consequence := C.theorem1_consequence
      theorem2_consequence := C.theorem2_consequence
      proposition1_consequence := C.proposition1_consequence
      proposition2_consequence := C.proposition2_consequence
      theorem3_field_formula :=
        theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel
          M.theorem3_field
      theorem3_constrained_alternative := ?_
      theorem3_fullSpace_statement := ?_ }
  · intro hC hContinuous hResponse xstar hConverges
    exact
      proof_theorem3_finite_fullSampledProjectedSourceSemantics_zero_or_no_aggregateFeasibleDirectionFormula
        M hC hContinuous hResponse hConverges
  · intro hUniv
    exact
      proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace
        M hUniv

theorem
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVFullProjectedPaperConsequences M := by
  exact
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics_ssgmConvergence
      M hSSGM

theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullPrimitiveSourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullPrimitiveSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  exact
    proof_finiteCoordinateILVFullPaperConsequences_of_fullSourceSemantics_ssgmConvergence
      M.toFullSourceSemantics S

theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullSampledSourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullSampledSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  exact
    proof_finiteCoordinateILVFullPaperConsequences_of_fullPrimitiveSourceSemantics_ssgmConvergence
      M.toPrimitiveSourceSemantics S

theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullPrimitiveSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullPrimitiveSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  exact
    proof_finiteCoordinateILVFullPaperConsequences_of_fullPrimitiveSourceSemantics_ssgmConvergence
      M hSSGM

theorem proof_finiteCoordinateILVFullPaperConsequences_of_fullSampledSourceSemantics
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullSampledSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVFullPaperConsequences E := by
  exact
    proof_finiteCoordinateILVFullPaperConsequences_of_fullSampledSourceSemantics_ssgmConvergence
      M hSSGM

theorem proof_coordinate_noncollision_of_forall_notMem_coordinateEqualityBadEvent
    {Coord : Type*} (trajectory ideal : ℕ → Coord → ℝ)
    (havoid :
      ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t)) :
    ∀ t i, trajectory t i ≠ ideal t i := by
  exact coordinate_noncollision_of_forall_notMem_coordinateEqualityBadEvent
    trajectory ideal havoid

theorem proof_conditionsC123_solutionSpace_condition
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : ConditionsC123 E) :
    E.solutionSpace_nonempty_bounded_closed_convex :=
  h.solutionSpace_condition

theorem proof_conditionsC123_uniqueIdealSolutions_condition
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : ConditionsC123 E) :
    E.uniqueIdealSolutions :=
  h.uniqueIdealSolutions_condition

theorem proof_conditionsC123_idealDistribution_condition
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : ConditionsC123 E) :
    E.idealDistribution_bounded_measurable_density :=
  h.idealDistribution_bounded_measurable_density_condition

def proof_finiteCoordinateC3Carrier_of_conditions
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteCoordinateIdealDistributionData Coord)
    (hC : ConditionsC123 E) :
    FiniteCoordinateC3Carrier E :=
  FiniteCoordinateC3Carrier.of_conditions D hC

theorem proof_finiteCoordinateC3Carrier_coordinate_noncollision_ae
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C : FiniteCoordinateC3Carrier E) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂C.data.idealMeasure, ∀ i, x i ≠ ideal i :=
  C.coordinate_noncollision_ae x

theorem proof_algorithm1_projected_update_formula
    {Point : Type*} (project : Point → Point) (raw next : Point) :
    Algorithm1ProjectedUpdate project raw next ↔ next = project raw := by
  exact algorithm1ProjectedUpdate_formula project raw next

theorem proof_finiteCoordinateDistance_l2_eq_zero_iff
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.l2 x y = 0 ↔ x = y := by
  exact finiteCoordinateDistance_l2_eq_zero_iff x y

/--
If a selected raw point is already feasible, finite `L2` norm projection leaves
it unchanged.  This is the zero-projection condition behind the paper's
unprojected displacement expansion.
-/
theorem proof_algorithm1_projected_update_eq_raw_of_l2_normProjection_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ} {raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hraw : raw ∈ E.solutionSpace) :
    next = raw := by
  exact algorithm1ProjectedUpdate_eq_raw_of_l2_normProjection_feasible
    hNorm hproject hupdate hraw

theorem proof_algorithm1_projected_update_increment_eq_raw_increment_of_l2_normProjection_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ}
    {center raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hraw : raw ∈ E.solutionSpace) :
    ∀ i : Coord, next i - center i = raw i - center i := by
  exact
    algorithm1ProjectedUpdate_increment_eq_raw_increment_of_l2_normProjection_feasible
      hNorm hproject hupdate hraw

theorem proof_algorithm1_projected_update_increment_eq_selectedResponse_increment_of_l2_normProjection_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ}
    {center raw next response : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hraw : raw ∈ E.solutionSpace)
    (hselected : raw = response) :
    ∀ i : Coord, next i - center i = response i - center i := by
  exact
    algorithm1ProjectedUpdate_increment_eq_selectedResponse_increment_of_l2_normProjection_feasible
      hNorm hproject hupdate hraw hselected

theorem proof_algorithm1_projected_updates_mem_of_projectionOnto
    {Point : Type*} {X : Set Point} {project : Point → Point}
    {raw trajectory : ℕ → Point}
    (hproject : ProjectionOnto X project)
    (h0 : trajectory 0 ∈ X)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    ∀ t : ℕ, trajectory t ∈ X := by
  exact algorithm1ProjectedUpdates_mem_of_projectionOnto hproject h0 hupdate

theorem proof_algorithm1_projected_updates_mem_solutionSpace_of_normProjection
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {project : Point → Point} {raw trajectory : ℕ → Point}
    (hproject : IsNormProjectionOnto E q project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact algorithm1ProjectedUpdates_mem_solutionSpace_of_normProjection
    hproject h0 hupdate

theorem proof_algorithm1_stop_condition_formula
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) :
    Algorithm1StopCondition E q trajectory T N t epsilon ↔
      t = T ∨ Algorithm1WindowStable E q trajectory t N epsilon := by
  exact algorithm1StopCondition_formula E q trajectory T N t epsilon

theorem proof_algorithm2_finite_projected_ssgm_update_formula
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (previous : Coord → ℝ) (radius : ℝ)
    (subgradient noise bias next : Coord → ℝ) :
    FiniteProjectedSSGMUpdateAt project previous radius
        subgradient noise bias next ↔
      next =
        project
          (fun i => previous i -
            radius * (subgradient i + noise i + bias i)) := by
  exact finiteProjectedSSGMUpdateAt_formula
    project previous radius subgradient noise bias next

theorem proof_ilvRadius_ssgmStepSizeConditions {r0 : ℝ} (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact ilvRadius_ssgmStepSizeConditions hr0

theorem proof_algorithm1_radius_ssgmStepSizeConditions {r0 : ℝ} (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact algorithm1_radius_ssgmStepSizeConditions hr0

theorem proof_followsFiniteProjectedSSGM_mem_of_projectionOnto
    {Coord : Type*} {X : Set (Coord → ℝ)}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    {subgradient noise bias : ℕ → Coord → ℝ}
    (hproject : ProjectionOnto X project)
    (hfollow :
      FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias)
    (h0 : trajectory 0 ∈ X) :
    ∀ t : ℕ, trajectory t ∈ X := by
  exact followsFiniteProjectedSSGM_mem_of_projectionOnto hproject hfollow h0

theorem proof_followsFiniteProjectedSampleSubgradientMethod_mem_of_projectionOnto
    {Coord : Type*} [Fintype Coord] {X : Set (Coord → ℝ)}
    {sampleCost : ℕ → (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    {subgradient noise bias : ℕ → Coord → ℝ}
    (hproject : ProjectionOnto X project)
    (hfollow :
      FollowsFiniteProjectedSampleSubgradientMethod sampleCost project
        trajectory radius subgradient noise bias)
    (h0 : trajectory 0 ∈ X) :
    ∀ t : ℕ, trajectory t ∈ X := by
  exact followsFiniteProjectedSampleSubgradientMethod_mem_of_projectionOnto
    hproject hfollow h0

theorem proof_followsFiniteProjectedSubgradientMethod_formula
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSubgradientMethod cost project trajectory radius
        subgradient noise bias ↔
      FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
        ∀ t : ℕ, FiniteSubgradientAt cost (trajectory t) (subgradient t) := by
  exact followsFiniteProjectedSubgradientMethod_formula
    cost project trajectory radius subgradient noise bias

theorem proof_followsFiniteProjectedSampleSubgradientMethod_formula
    {Coord : Type*} [Fintype Coord]
    (sampleCost : ℕ → (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSampleSubgradientMethod sampleCost project trajectory
        radius subgradient noise bias ↔
      FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
        ∀ t : ℕ,
          FiniteSubgradientAt (sampleCost t) (trajectory t) (subgradient t) := by
  exact followsFiniteProjectedSampleSubgradientMethod_formula
    sampleCost project trajectory radius subgradient noise bias

theorem proof_followsFiniteProjectedSSGM_zero_noise_bias_formula
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSSGM project trajectory radius subgradient
        (fun _t _i => 0) (fun _t _i => 0) ↔
      ∀ t : ℕ,
        trajectory (t + 1) =
          project (fun i =>
            trajectory t i - radius (t + 1) * subgradient t i) := by
  exact followsFiniteProjectedSSGM_zero_noise_bias_formula
    project trajectory radius subgradient

theorem proof_finiteSubgradientAt_of_convexOn_univ_hasFDerivAt
    {Coord : Type*} [Fintype Coord]
    {cost : (Coord → ℝ) → ℝ} {x g : Coord → ℝ}
    (hconv : ConvexOn ℝ Set.univ cost)
    (hderiv :
      HasFDerivAt cost
        (EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional g) x) :
    FiniteSubgradientAt cost x g := by
  exact finiteSubgradientAt_of_convexOn_univ_hasFDerivAt hconv hderiv

theorem proof_finiteSubgradientAt_lpCostGradientCandidate_of_convexOn
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p) {x ideal : Coord → ℝ}
    (hcoord : ∀ i, x i ≠ ideal i)
    (hconv :
      ConvexOn ℝ Set.univ
        (fun y : Coord → ℝ =>
          EconCSLib.FiniteDimensionalNorms.lp p
            (fun i => y i - ideal i))) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      x
      (lpCostGradientCandidate p (fun i => x i - ideal i)) := by
  exact finiteSubgradientAt_lpCostGradientCandidate_of_convexOn
    hp hcoord hconv

theorem proof_convexOn_univ_finiteCoordinate_lp_cost
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 1 ≤ p) (ideal : Coord → ℝ) :
    ConvexOn ℝ Set.univ
      (fun y : Coord → ℝ =>
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i)) := by
  exact convexOn_univ_finiteCoordinate_lp_cost hp ideal

theorem proof_finiteSubgradientAt_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p) {x ideal : Coord → ℝ}
    (hcoord : ∀ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      x
      (lpCostGradientCandidate p (fun i => x i - ideal i)) := by
  exact finiteSubgradientAt_lpCostGradientCandidate hp hcoord

theorem proof_modelB_neg_lpCostGradientCandidate_boundary_distance
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hcoord : ∀ i, center i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    finiteCoordinateDistance (SourceNorm.lp q) response center = |r| := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance
    hdual hcoord hresponse

theorem proof_modelB_neg_lpCostGradientCandidate_boundary_distance_of_notMem_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (havoid : ideal ∉ coordinateEqualityBadEvent center)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    finiteCoordinateDistance (SourceNorm.lp q) response center = |r| := by
  exact
    modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance_of_notMem_badEvent
      hdual havoid hresponse

theorem proof_modelB_neg_lpCostGradientCandidate_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) :
    ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response ↔
      response =
        fun i => center i - r *
          lpCostGradientCandidate p (fun j => center j - ideal j) i := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_formula
    hdual hcoord r response

theorem proof_finiteCoordinate_localNeighborhood_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) (q : SourceNorm)
    (center candidate : Coord → ℝ) (r : ℝ) :
    candidate ∈ LocalNeighborhood E q center r ↔
      candidate ∈ E.solutionSpace ∧
        finiteCoordinateDistance q candidate center ≤ r := by
  exact finiteCoordinate_localNeighborhood_formula E hNorm q center candidate r

theorem proof_localNeighborhood_mem_solutionSpace
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {center candidate : Point} {r : ℝ}
    (hmem : candidate ∈ LocalNeighborhood E q center r) :
    candidate ∈ E.solutionSpace := by
  exact localNeighborhood_mem_solutionSpace hmem

theorem proof_localNeighborhood_normDistance_le
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {center candidate : Point} {r : ℝ}
    (hmem : candidate ∈ LocalNeighborhood E q center r) :
    E.normDistance q candidate center ≤ r := by
  exact localNeighborhood_normDistance_le hmem

theorem proof_localNeighborhood_mono_radius
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {center candidate : Point} {r R : ℝ}
    (hrR : r ≤ R)
    (hmem : candidate ∈ LocalNeighborhood E q center r) :
    candidate ∈ LocalNeighborhood E q center R := by
  exact localNeighborhood_mono_radius hrR hmem

theorem proof_finiteCoordinate_mem_localNeighborhood_self_l1
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E SourceNorm.l1 center r := by
  exact finiteCoordinate_mem_localNeighborhood_self_l1 E hNorm hcenter hr

theorem proof_finiteCoordinate_mem_localNeighborhood_self_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E SourceNorm.l2 center r := by
  exact finiteCoordinate_mem_localNeighborhood_self_l2 E hNorm hcenter hr

theorem proof_finiteCoordinate_mem_localNeighborhood_self_linf
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E SourceNorm.linfty center r := by
  exact finiteCoordinate_mem_localNeighborhood_self_linf E hNorm hcenter hr

theorem proof_finiteCoordinate_mem_localNeighborhood_self_lp
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : ℝ} (hp : 0 < p)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E (SourceNorm.lp p) center r := by
  exact finiteCoordinate_mem_localNeighborhood_self_lp E hNorm hp hcenter hr

theorem proof_modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hmem : response ∈ E.solutionSpace)
    (hcoord : ∀ i, center i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    response ∈ LocalNeighborhood E (SourceNorm.lp q) center r := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood
    E hNorm hdual hr hmem hcoord hresponse

theorem proof_modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood_of_notMem_badEvent
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hmem : response ∈ E.solutionSpace)
    (havoid : ideal ∉ coordinateEqualityBadEvent center)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    response ∈ LocalNeighborhood E (SourceNorm.lp q) center r := by
  exact
    modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood_of_notMem_badEvent
      E hNorm hdual hr hmem havoid hresponse

theorem proof_hasFDerivAt_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    HasFDerivAt
      (fun y : Coord → ℝ =>
        -EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      (EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i)) x := by
  exact hasFDerivAt_neg_lpCostGradientCandidate hp hcoord

theorem proof_modelB_neg_lpCostGradientCandidate_projected_ssgm_update
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {previous ideal raw next : Coord → ℝ} (radius : ℝ)
    (hcoord : ∀ i, previous i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) previous radius
        (fun i => -lpCostGradientCandidate p (fun j => previous j - ideal j) i) raw)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (lpCostGradientCandidate p (fun i => previous i - ideal i))
      (fun _ => 0) (fun _ => 0) next := by
  exact finiteProjectedSSGMUpdateAt_of_modelBFiniteResponseAt_neg_lpCostGradientCandidate
    hdual project radius hcoord hresponse hproject

theorem proof_followsFiniteProjectedSSGM_of_modelBFiniteResponses_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSSGM project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact followsFiniteProjectedSSGM_of_modelBFiniteResponses_neg_lpCostGradientCandidate
    hdual project hcoord hresponse hproject

theorem proof_followsFiniteProjectedSubgradientMethod_of_modelBFiniteResponses_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (cost : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1)))
    (hsubgradient :
      ∀ t : ℕ,
        FiniteSubgradientAt cost (trajectory t)
          (lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))) :
    FollowsFiniteProjectedSubgradientMethod cost project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact
    followsFiniteProjectedSubgradientMethod_of_modelBFiniteResponses_neg_lpCostGradientCandidate
      hdual cost project hcoord hresponse hproject hsubgradient

theorem proof_followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hconv :
      ∀ t : ℕ,
        ConvexOn ℝ Set.univ
          (fun y : Coord → ℝ =>
            EconCSLib.FiniteDimensionalNorms.lp p
              (fun i => y i - ideal t i)))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
      project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses
    hdual project hcoord hconv hresponse hproject

theorem proof_followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_noConvex
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
      project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses'
    hdual project hcoord hresponse hproject

theorem proof_followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
      project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact
    followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent
      hdual project havoid hresponse hproject

theorem proof_followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hprojectOnto : ProjectionOnto E.solutionSpace project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory radius
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact
    followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace
      E hdual hprojectOnto h0 havoid hresponse hproject

theorem proof_followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace_of_normProjection
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hprojectNorm : IsNormProjectionOnto E (SourceNorm.lp q) project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory radius
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact
    followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace_of_normProjection
      E hdual hprojectNorm h0 havoid hresponse hproject

theorem proof_lpCostGradientCandidate_lq_norm_eq_one_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p q : ℝ} (hdual : HolderDualFinite p q) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      finiteCoordinateNorm (SourceNorm.lp q)
        (lpCostGradientCandidate p (fun i => x i - ideal i)) = 1 := by
  exact
    FiniteCoordinateIdealDistributionData.lpCostGradientCandidate_lq_norm_eq_one_ae
      D hdual x

theorem proof_finiteSubgradientAt_lpCostGradientCandidate_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p : ℝ} (hp : 1 < p) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal i))
        x
        (lpCostGradientCandidate p (fun i => x i - ideal i)) := by
  exact
    FiniteCoordinateIdealDistributionData.finiteSubgradientAt_lpCostGradientCandidate_ae
      D hp x

theorem proof_modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p q : ℝ} (hdual : HolderDualFinite p q) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      modelBFiniteNormalizedDirection (SourceNorm.lp q)
        (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i) =
          fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i := by
  exact
    FiniteCoordinateIdealDistributionData.modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self_ae
      D hdual x

theorem proof_modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center : Coord → ℝ} {r : ℝ}
    (response : (Coord → ℝ) → Coord → ℝ)
    (hresponse :
      ∀ ideal,
        ModelBFiniteResponseAt (SourceNorm.lp q) center r
          (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
          (response ideal)) :
    ∀ᵐ ideal ∂D.idealMeasure,
      finiteCoordinateDistance (SourceNorm.lp q) (response ideal) center = |r| := by
  exact
    FiniteCoordinateIdealDistributionData.modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance_ae
      D hdual response hresponse

theorem proof_finiteModelAILVTrace_raw_mem_localNeighborhood
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0) (t : ℕ) :
    T.raw t ∈
      LocalNeighborhood E q (E.trajectory q VoterResponseModel.modelA t)
        (ilvRadius r0 (t + 1)) := by
  exact T.raw_mem_localNeighborhood t

theorem proof_finiteModelAILVTrace_raw_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0) (t : ℕ) :
    T.raw t ∈ E.solutionSpace := by
  exact T.raw_mem_solutionSpace t

theorem proof_finiteModelAILVTrace_trajectory_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0) :
    ∀ t : ℕ, E.trajectory q VoterResponseModel.modelA t ∈ E.solutionSpace := by
  exact T.trajectory_mem_solutionSpace

theorem proof_finiteModelAILVTrace_raw_normDistance_le_center_of_center_mem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (t : ℕ)
    (hcenter :
      E.trajectory q VoterResponseModel.modelA t ∈
        LocalNeighborhood E q
          (E.trajectory q VoterResponseModel.modelA t)
          (ilvRadius r0 (t + 1))) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p (E.trajectory q VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_of_center_mem hUtil t hcenter

theorem proof_finiteModelAILVTrace_raw_normDistance_le_center_l1
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {r0 : ℝ}
    (T : FiniteModelAILVTrace E SourceNorm.l1 r0)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory SourceNorm.l1 VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_l1 hNorm hUtil hr0 t

theorem proof_finiteModelAILVTrace_raw_normDistance_le_center_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {r0 : ℝ}
    (T : FiniteModelAILVTrace E SourceNorm.l2 r0)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_l2 hNorm hUtil hr0 t

theorem proof_finiteModelAILVTrace_raw_normDistance_le_center_linf
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {r0 : ℝ}
    (T : FiniteModelAILVTrace E SourceNorm.linfty r0)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory SourceNorm.linfty VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_linf hNorm hUtil hr0 t

theorem proof_finiteModelAILVTrace_raw_normDistance_le_center_lp
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q r0 : ℝ}
    (T : FiniteModelAILVTrace E (SourceNorm.lp q) r0)
    (hNorm : UsesFiniteCoordinateNormDistance E) (hq : 0 < q)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_lp hNorm hq hUtil hr0 t

theorem proof_finiteProjectedSampleSubgradientMethod_lpCost_modelB_with_ilvRadius_ssgmInputs
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    {p q r0 : ℝ} (hdual : HolderDualFinite p q) (hr0 : 0 < r0)
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory ideal raw : ℕ → Coord → ℝ}
    (hprojectNorm : IsNormProjectionOnto E (SourceNorm.lp q) project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t)
          (ilvRadius r0 (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    SSGMStepSizeConditions (ilvRadius r0) ∧
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory (ilvRadius r0)
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact
    finiteProjectedSampleSubgradientMethod_lpCost_modelB_with_ilvRadius_ssgmInputs
      E hdual hr0 hprojectNorm h0 havoid hresponse hproject

theorem proof_finiteModelBILVTrace_ssgmInputs
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) ∧
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - T.ideal t i))
        T.project
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB)
        (ilvRadius r0)
        (fun t =>
          lpCostGradientCandidate p
            (fun i =>
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
                T.ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
          E.solutionSpace := by
  exact T.ssgmInputs hdual hr0

theorem proof_finiteModelBILVTrace_ssgmStepSizeConditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact T.ssgmStepSizeConditions hdual hr0

theorem proof_finiteModelBILVTrace_followsSampleSubgradientMethod
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        EconCSLib.FiniteDimensionalNorms.lp p (fun i => y i - T.ideal t i))
      T.project
      (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB)
      (ilvRadius r0)
      (fun t =>
        lpCostGradientCandidate p
          (fun i =>
            E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
              T.ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact T.followsSampleSubgradientMethod hdual hr0

theorem proof_finiteModelBILVTrace_trajectory_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    ∀ t : ℕ,
      E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
        E.solutionSpace := by
  exact T.trajectory_mem_solutionSpace hdual hr0

theorem proof_theorem2FiniteSSGMBridge_ssgmInputs
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q)
    (hdual : HolderDualFinite p q) :
    SSGMStepSizeConditions (ilvRadius B.r0) ∧
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          EconCSLib.FiniteDimensionalNorms.lp p
            (fun i => y i - B.trace.ideal t i))
        B.trace.project
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB)
        (ilvRadius B.r0)
        (fun t =>
          lpCostGradientCandidate p
            (fun i =>
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
                B.trace.ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
          E.solutionSpace := by
  exact B.ssgmInputs hdual

theorem proof_theorem2FiniteSSGMBridge_coordinate_noncollision_ae
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂B.c3.data.idealMeasure, ∀ i, x i ≠ ideal i := by
  exact B.coordinate_noncollision_ae x

def proof_theorem2SourceToFiniteSSGMBridge_finite_bridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (B : Theorem2SourceToFiniteSSGMBridge E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    Theorem2FiniteSSGMBridge E p q := by
  exact B.finite_bridge hC hUtil hResponse hdual

theorem proof_modelAResponseAt_lpNormedUtilities_normDistance_le_candidate
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    {center candidate response : Point} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E q center r voter response)
    (hcandidate : candidate ∈ LocalNeighborhood E q center r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p candidate (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_candidate
    E p q hUtil hresponse hcandidate

theorem proof_modelAResponseAt_lpNormedUtilities_normDistance_le_center
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    {center response : Point} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E q center r voter response)
    (hcenter : center ∈ LocalNeighborhood E q center r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_center
    E p q hUtil hresponse hcenter

theorem proof_finiteCoordinate_modelAResponseAt_normDistance_le_center_l1
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E SourceNorm.l1 center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l1
    E hNorm hUtil hresponse hcenter hr

theorem proof_finiteCoordinate_modelAResponseAt_normDistance_le_center_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E SourceNorm.l2 center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l2
    E hNorm hUtil hresponse hcenter hr

theorem proof_finiteCoordinate_modelAResponseAt_normDistance_le_center_linf
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_linf
    E hNorm hUtil hresponse hcenter hr

theorem proof_finiteCoordinate_modelAResponseAt_normDistance_le_center_lp
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {q : ℝ} (hq : 0 < q)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E (SourceNorm.lp q) center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_lp
    E hNorm hq hUtil hresponse hcenter hr

theorem proof_modelAResponseAt_theorem1NormPair_normDistance_le_center
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p q : SourceNorm} (hpq : Theorem1NormPair p q)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E q center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_theorem1NormPair_lpNormedUtilities_normDistance_le_center
    E hNorm hpq hUtil hresponse hcenter hr

theorem proof_finiteCoordinate_modelAResponseAt_l1_linf_distance_le_center
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.l1 response (E.ideal voter) ≤
      finiteCoordinateDistance SourceNorm.l1 center (E.ideal voter) := by
  exact finiteCoordinate_modelAResponseAt_l1_linf_distance_le_center
    E hNorm hUtil hresponse hcenter hr

theorem proof_finiteCoordinate_modelAResponseAt_linf_l1_distance_le_center
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    (hresponse : ModelAResponseAt E SourceNorm.l1 center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.linfty response (E.ideal voter) ≤
      finiteCoordinateDistance SourceNorm.linfty center (E.ideal voter) := by
  exact finiteCoordinate_modelAResponseAt_linf_l1_distance_le_center
    E hNorm hUtil hresponse hcenter hr

theorem proof_finiteSubgradientAt_l1Cost_unitSignCandidate
    {Coord : Type*} [Fintype Coord]
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        EconCSLib.FiniteDimensionalNorms.l1 (fun i => y i - ideal i))
      x
      (fun i => (x i - ideal i) / |x i - ideal i|) := by
  exact finiteSubgradientAt_l1Cost_unitSignCandidate hcoord

theorem proof_finiteCoordinateNorm_linf_l1CostUnitSign_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    finiteCoordinateNorm SourceNorm.linfty
      (fun i => (x i - ideal i) / |x i - ideal i|) = 1 := by
  exact finiteCoordinateNorm_linf_l1CostUnitSign_eq_one hcoord

theorem proof_finiteSubgradientAt_linfCost_singleActiveCoordinate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {x ideal : Coord → ℝ} {i0 : Coord}
    (hmax : ∀ i, |x i - ideal i| ≤ |x i0 - ideal i0|)
    (hnz : x i0 ≠ ideal i0) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        EconCSLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      x
      (fun i => if i = i0 then
          (x i0 - ideal i0) / |x i0 - ideal i0| else 0) := by
  exact finiteSubgradientAt_linfCost_singleActiveCoordinate hmax hnz

theorem proof_finiteCoordinateNorm_l1_singleActiveSign_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {x ideal : Coord → ℝ} {i0 : Coord}
    (hnz : x i0 ≠ ideal i0) :
    finiteCoordinateNorm SourceNorm.l1
      (fun i => if i = i0 then
        (x i0 - ideal i0) / |x i0 - ideal i0| else 0) = 1 := by
  exact finiteCoordinateNorm_l1_singleActiveSign_eq_one hnz

end GKGMM19IterativeLocalVoting
