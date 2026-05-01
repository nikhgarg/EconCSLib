# Foundations: Optimization

Use for `EconCSLib/Foundations/Optimization/*`, argmax existence, objective
comparison wrappers, finite rule optimization, and paper-facing optimality
statements.

## Proof Seams

- For finite deterministic-rule optimization statements, first prove a generic
  maximizer-existence theorem over the finite function type
  `(instances -> actions)`. Keep paper folders responsible for defining the
  paper-specific objective and applying the generic result.
- For expected objective wrappers, separate the deterministic objective from
  the expectation operator. Prove a monotone/linear expectation interface once,
  then instantiate paper theorems by rewriting the expected paper objective to
  the generic expected objective.
- For paper statements that say an optimizer exists, avoid hiding the optimizer
  in an opaque certificate. Prove the argmax/existence theorem in the generic
  library and make the paper theorem a thin wrapper with exact assumptions.
- For LP sparsity or BFS-style results, separate the linear-programming theorem
  from finite counting consequences. Encode the active-support bound first,
  then prove reusable counting lemmas over finite supports.
- For normalized objective values, prove boundedness before compactness or
  supremum reasoning. Finite PMF expectations are often bounded by row maxima,
  giving immediate `BddAbove` side conditions.
- For optimization reductions, prove lift/descend functional preservation,
  symmetrization dominance, and then `sSup` equality from explicit nonempty and
  bounded-above feasible-value conditions.

## Lean Patterns

- If an optimizer proof over functions becomes unwieldy, introduce a finite
  coded feasible type and decode after using `Fintype`.
- Keep objective aliases paper-facing and formula-explicit; push only the
  reusable argmax/ordering theorem into the library.
- When comparing objectives, expose monotonicity as a named field or theorem
  rather than unfolding expectation internals inside every paper wrapper.
