# Algorithmic Complexity Proof Guidance

Use this reference for EC formalizations that cite NP-hardness, approximation
hardness, polynomial-time reductions, randomized classes, or consequences such
as `NP = ZPP`.

## Separation of Concerns

Keep three layers distinct:

- Compile the paper's concrete reductions in Lean: instance maps, feasibility
  preservation, objective preservation, threshold-decision preservation,
  solver transfer, and approximation-ratio preservation.
- Represent missing machine-level facts as explicit external hypotheses or
  abstract class models when the repo does not yet contain a Turing-machine or
  runtime semantics.
- Do not mark native NP-hardness or randomized-class consequences as fully
  formalized until the underlying class semantics and cited hardness theorem
  are formalized or imported.

For classic hardness results, a good stopping point is a paper-facing theorem
surface that proves every reduction and exposes a narrow external-consequence
wrapper. The README/DAG/handoff should say exactly which machine-level theorem
is still external.

## Reusable Lean Shapes

Prefer reusable library interfaces over paper-local ad hoc predicates:

- `DecisionProblem`: languages over an instance type.
- `ManyOneReduction`: correctness of an instance map.
- `PolynomialTimeReduction`: a many-one reduction plus an abstract runtime
  predicate supplied by a future machine model.
- `ExternalReductionConsequence` and
  `ExternalPolynomialReductionConsequence`: wrappers for consequences supplied
  by external hardness facts.
- `ReductionClosedHardness` and `PolynomialReductionClosedHardness`: abstract
  hardness transfer when the downstream paper only needs closure under
  reductions.
- `ExternalSolverConsequence`: solver hardness or collapse consequences for
  optimization/approximation algorithms.
- `RandomizedComplexityClassModel`: abstract `P`, `NP`, `RP`, `co-RP`, `ZPP`,
  and `co-NP` relationships when the source includes a complexity-class note
  but the repo lacks machine semantics.

Keep the abstract class model honest: its fields are assumptions about class
relationships, not proofs of machine semantics.

## Paper-Facing Wrapper Pattern

Expose the source route in small wrappers, even when the final theorem is
already closed:

- Primitive encoding correctness: feasibility and objective value.
- Threshold-decision correctness: source decision instance iff target decision
  instance.
- Many-one and polynomial-time reduction objects.
- Solver-transfer theorem for exact optimization.
- Solver-transfer theorem for approximation guarantees.
- Hardness-transfer theorem through a reduction-closed hardness predicate.
- External-consequence theorem for a cited hardness or inapproximability fact.
- Named class-collapse specialization if the source states one explicitly.

This lets future reviewers see which part was Lean-checked and which part is
the imported or abstract complexity premise.

## When to Stop

Stop at the external complexity boundary when all source-specific reductions
and auction/algorithmic endpoints compile and the only missing content is a
general-purpose machine model or a famous external theorem such as Karp or
Hastad. Record that as a library project, not as an unfinished paper-specific
proof seam.

Before handoff:

- Name the exact external theorem(s) still needed.
- Name the current Lean wrappers that would consume those theorems.
- Say whether theorem status is `formalized`, `conditional`, or `partially
  formalized` under `docs/STATUS.md`.
- Add a validation command set and a review-slice count if the paper exposes a
  large `PaperInterface.lean`.
