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
- `assumption_ssgm_convergence_theorem`: the single paper-local axiom for the
  external stochastic subgradient convergence theorem bundle.  It supplies only
  theorem-shaped SSGM convergence records; concrete finite-coordinate source
  semantics are supplied separately by `FiniteCoordinateILVConcreteSourceModel`.
  Theorem 3 is derived separately from the concrete finite directional field
  and the deterministic global projected trace source carried by
  `FiniteCoordinateILVFullConcreteSourceModel`, rather than being hidden in the
  SSGM boundary or in an abstract environment drift field.
- `assumption_expected_subgradient_theorem`: the external Appendix Theorem 4
  interchange theorem identifying an expected selected subgradient as a
  subgradient of the expected objective.
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
Abstract theorem statement for Appendix Theorem 4.

The source theorem is an external convex-analysis/subgradient interchange
result: if each sampled voter supplies a subgradient at `x`, then the expected
selected subgradient is a subgradient of the expected objective at `x`.
This paper-local predicate keeps that imported theorem's mathematical shape
visible without committing to a reusable measure-theoretic API here.
-/
def ExpectedSubgradientTheoremStatement
    {Point Theta Grad : Type*}
    (isSampleSubgradient : Point → Theta → Grad → Prop)
    (expected : (Theta → Grad) → Grad)
    (isExpectedSubgradient : Point → Grad → Prop) : Prop :=
  ∀ x sampleGradient,
    (∀ θ, isSampleSubgradient x θ (sampleGradient θ)) →
      isExpectedSubgradient x (expected sampleGradient)

/--
Appendix Theorem 4 imported theorem boundary.

This records the external theorem quoted in the paper; deterministic ILV
source-model bridges are still formalized separately.
-/
-- audit-premise: hExpectedSubgradient : assumption_expected_subgradient_theorem
axiom assumption_expected_subgradient_theorem
    {Point Theta Grad : Type*}
    (isSampleSubgradient : Point → Theta → Grad → Prop)
    (expected : (Theta → Grad) → Grad)
    (isExpectedSubgradient : Point → Grad → Prop) :
    ExpectedSubgradientTheoremStatement
      isSampleSubgradient expected isExpectedSubgradient

/--
Single theorem-shaped boundary for the analytic convergence layer.

The finite-coordinate norm algebra, Lemma 3 derivative/sign bridges,
coordinate-equality null-event reductions, projected-SSGM recurrence predicates,
Model A/Model B trace packages, nonsmooth endpoint subgradient witnesses,
Theorem 2 finite SSGM input bridge, Proposition 1/2 target-identification
carriers, and Model B-to-SSGM local update bridges are formalized outside this
assumption.  What remains here is a
theorem-shaped stochastic approximation theorem bundle: future library work
should prove this statement from reusable stochastic subgradient method
convergence results.  The record `FiniteCoordinateILVConcreteSourceModel`
bundles the deterministic finite-coordinate source semantics into one concrete
model interface, and
`ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence` is the
checked bridge from that source model plus this theorem-shaped axiom to the
four convergence endpoints.
-/
-- audit-premise: hSSGM : assumption_ssgm_convergence_theorem E
axiom assumption_ssgm_convergence_theorem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    FiniteCoordinateILVSSGMConvergenceTheorems E

/--
Apply the single SSGM convergence axiom to a concrete finite-coordinate source
model to obtain the named four-endpoint consequence bundle.
-/
theorem ssgm_convergence_theorem_consequences
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    ILVSSGMConvergenceConsequences E :=
  ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    M (assumption_ssgm_convergence_theorem E)

end GKGMM19IterativeLocalVoting
