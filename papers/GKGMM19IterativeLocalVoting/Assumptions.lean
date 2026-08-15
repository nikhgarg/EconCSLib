import EconCSLib.Foundations.Optimization.ExpectedSubgradient
import GKGMM19IterativeLocalVoting.MainTheorems

/-!
# Paper Assumptions: Iterative Local Voting for Collective Decision-making in Continuous Spaces

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

## Paper Assumptions

- `assumption_conditions_c123`: source assumptions C1, C2, and C3.
- `assumption_ssgm_convergence_theorem`: the single paper-local boundary for the
  external stochastic subgradient convergence theorem bundle, carried as an
  explicit premise rather than an axiom.  It supplies only theorem-shaped SSGM
  convergence records; concrete finite-coordinate source semantics are supplied
  separately by `FiniteCoordinateILVConcreteSourceModel`.
  Theorem 3 is derived separately from the concrete finite directional field
  and the deterministic global projected trace source carried by
  `FiniteCoordinateILVFullConcreteSourceModel`, rather than being hidden in the
  SSGM boundary or in an abstract environment drift field.
- `expected_subgradient_theorem`: Appendix Theorem 4, the interchange result
  identifying an expected selected subgradient as a subgradient of the expected
  objective.  This is proved, not assumed.
-/

namespace GKGMM19IterativeLocalVoting

/--
Source assumptions C1, C2, and C3 from Section 3:
nonempty bounded closed convex solution space, unique ideal points, and a
bounded measurable density for independently drawn ideal points.
-/
-- audit-premise: hC : assumption_conditions_c123 E
abbrev assumption_conditions_c123 {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  E.solutionSpace_nonempty_bounded_closed_convex ∧
    E.uniqueIdealSolutions ∧
      E.idealDistribution_bounded_measurable_density

/--
Appendix Theorem 4, stated concretely.

The source theorem is a convex-analysis/subgradient interchange result: if each
sampled voter supplies a subgradient at `x`, then the expected selected
subgradient is a subgradient of the expected objective at `x`.

This is stated at the concrete finite-coordinate instantiation the paper uses,
so that "is a subgradient" and "expected" refer to the actual subgradient
inequality and the actual Bochner integral.  It is therefore a theorem, proved
in `EconCSLib.Foundations.Optimization.ExpectedSubgradient`, rather than a
postulate.
-/
def ExpectedSubgradientTheoremStatement
    {Coord Theta : Type*} [Fintype Coord] [MeasurableSpace Theta]
    (μ : MeasureTheory.Measure Theta)
    (cost : Theta → (Coord → ℝ) → ℝ) : Prop :=
  ∀ (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ),
    (∀ᵐ θ ∂μ, FiniteSubgradientAt (cost θ) x (sampleGradient θ)) →
      (∀ y, MeasureTheory.Integrable (fun θ => cost θ y) μ) →
        (∀ i, MeasureTheory.Integrable (fun θ => sampleGradient θ i) μ) →
          FiniteSubgradientAt (fun y => ∫ θ, cost θ y ∂μ) x
            (fun i => ∫ θ, sampleGradient θ i ∂μ)

/--
Appendix Theorem 4, proved.

Previously this was a paper-local `axiom` quantified over three unrelated
abstract predicates, which made it inconsistent: instantiating
`isSampleSubgradient` as always true and `isExpectedSubgradient` as always false
derived `False`.  The statement is now tied to the real subgradient inequality
and integral, and discharged from the reusable library theorem.
-/
theorem expected_subgradient_theorem
    {Coord Theta : Type*} [Fintype Coord] [MeasurableSpace Theta]
    (μ : MeasureTheory.Measure Theta)
    (cost : Theta → (Coord → ℝ) → ℝ) :
    ExpectedSubgradientTheoremStatement μ cost := by
  intro x sampleGradient hsub hcost hgrad
  exact EconCSLib.Optimization.finiteSubgradientAt_integral hsub hcost hgrad

/--
Single theorem-shaped boundary for the analytic convergence layer.

The finite-coordinate norm algebra, Lemma 3 derivative/sign bridges,
coordinate-equality null-event reductions, projected-SSGM recurrence predicates,
Model A/Model B trace packages, nonsmooth endpoint subgradient witnesses,
Theorem 2 finite SSGM input bridge, Proposition 1/2 target-identification
carriers, and Model B-to-SSGM local update bridges are formalized outside this
boundary.  What remains here is a theorem-shaped stochastic approximation
bundle: future library work should prove this statement from reusable
stochastic subgradient method convergence results.

This is deliberately **not** an `axiom`.  `ILVEnvironment.convergesWithProbabilityOne`
is a free field of the environment, so asserting
`FiniteCoordinateILVSSGMConvergenceTheorems E` for an arbitrary `E` is not
merely unproved, it is refutable: instantiating that field as `fun _ _ => False`
while satisfying every hypothesis field derives `False`.  The boundary is
therefore carried as an explicit premise, which keeps the paper's endpoint
theorems conditional and the development consistent.

The record `FiniteCoordinateILVConcreteSourceModel` bundles the deterministic
finite-coordinate source semantics into one concrete model interface, and
`ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence` is the
checked bridge from that source model plus this boundary premise to the four
convergence endpoints.
-/
-- audit-premise: hSSGM : assumption_ssgm_convergence_theorem E
abbrev assumption_ssgm_convergence_theorem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  FiniteCoordinateILVSSGMConvergenceTheorems E

/--
Apply the SSGM convergence boundary premise to a concrete finite-coordinate
source model to obtain the named four-endpoint consequence bundle.
-/
theorem ssgm_convergence_theorem_consequences
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    ILVSSGMConvergenceConsequences E :=
  ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence M hSSGM

end GKGMM19IterativeLocalVoting
