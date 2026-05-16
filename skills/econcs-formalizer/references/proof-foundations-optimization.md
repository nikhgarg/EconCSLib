# Foundations: Optimization

Use for `EconCSLib/Foundations/Optimization/*`, argmax existence, objective
comparison wrappers, finite rule optimization, and paper-facing optimality
statements.

Start with `docs/OPTIMIZATION_LIBRARY_ROADMAP.md` when deciding whether an
optimization proof seam should stay paper-local or move to `EconCSLib`.

## Proof Seams

- For "candidate plus universal bound" proofs, use
  `EconCSLib.Optimization.UpperBoundCertificate` for maximization and
  `EconCSLib.Optimization.LowerBoundCertificate` for minimization. These are
  the preferred wrappers for paper LP certificates, exchange upper bounds,
  endpoint/current-bound certificates, and finite lower-bound arguments.
- Use `StrictUpperBoundCertificate` / `StrictLowerBoundCertificate` when the
  paper also proves uniqueness or a strict structure theorem away from the
  candidate. Keep equality-case algebra paper-local until a second paper needs
  the same condition.
- For finite deterministic-rule optimization statements, first prove a generic
  maximizer-existence theorem over the finite function type
  `(instances -> actions)`. Keep paper folders responsible for defining the
  paper-specific objective and applying the generic result.
- For finite feasible regions that are awkward to optimize over directly, use
  `exists_isMaximizerOn_of_finite_code` or
  `exists_isMinimizerOn_of_finite_code`: define a finite code type, prove every
  feasible code decodes to a feasible object, and prove every source-feasible
  object is covered by some feasible code.
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
- For finite LP-heavy papers where a full solver would be overkill, define the
  exact paper-local equality-form or epigraph LP; prove weak duality for the
  exact variables; construct the closed-form primal witness; construct the
  matching dual/certificate; prove feasibility, tightness/complementary
  slackness, and uniqueness; then finish with an `UpperBoundCertificate` or
  `LowerBoundCertificate` and wrap this as the paper theorem. This can fully
  verify a source result without a generic LP solver when the final wrapper
  constructs or discharges every certificate internally. Generalize the LP
  record only after a second paper needs the same constraint shape.
- For standard finite maximization LPs with `x >= 0` and `Ax <= b`, use
  `StandardMaxLP.weak_duality` and `StandardMaxLPCertificate.isMaximizerOn`.
  This is the right first abstraction for GCG-style closed primal/dual
  certificates. Full basic-feasible-solution/rank support is heavier; add it
  only when a source theorem needs the BFS support-size statement itself.
- For online-auction or primal-dual competitive-ratio proofs, separate the
  generic sandwich from the paper accounting. Use
  `UpperBoundApproximationCertificate` when `benchmark <= dual` and
  `ratio * dual <= achieved`; use
  `UpperBoundApproximationWithErrorCertificate` for small-bids or finite-error
  variants.
- For auction lower bounds by hard input distributions, prefer the generic Yao
  certificate `EconCSLib.Decision.RandomizedUpperPayoffCertificate`; keep
  source-specific permutation, layer-count, or benchmark-normalization fields
  in the paper folder.
- For normalized objective values, prove boundedness before compactness or
  supremum reasoning. Finite PMF expectations are often bounded by row maxima,
  giving immediate `BddAbove` side conditions.
- For optimization reductions, prove lift/descend functional preservation,
  symmetrization dominance, and then `sSup` equality from explicit nonempty and
  bounded-above feasible-value conditions.
- For exchange proofs over integer allocations, state the local move relation
  explicitly. Prove "global optimum has no improving move" immediately from
  `IsMaximizerOn`, and only prove the harder converse after establishing the
  feasible move graph is connected by those moves. Once reachability is
  available, finish with `isMaximizerOn_of_reachable_nonincreasing` or
  `isMinimizerOn_of_reachable_nondecreasing`.
- For continuous-paper proofs that say "approximate by a finite object, apply
  local endpoint/exchange moves until a canonical object remains, then pass to
  a limit", split the seam into three reusable facts instead of repeatedly
  unfolding the source prose: a finite descent theorem over a natural-valued
  complexity, an arbitrary-close finite-seed bridge, and a compact/canonical
  maximizer bridge showing the original target value is attained or exceeded.
  Keep the paper-specific work in the one-step move certificate; this avoids
  token-heavy rewrites of the same termination and epsilon/maximizer argument.
- When the approximation seeds are bounded but the canonical objects may be
  unbounded, do not use the bounded seed type as the descent domain.  Embed the
  bounded seeds into a finite coded domain that also represents rays, tails, or
  the full feasible domain, then state descent and maximizer data over that
  larger domain.  This prevents a later impossible maximizer/canonical-shape
  obligation for accept-all or tail policies.
- Do not assume raw component count is the right descent measure.  If a proof
  step can jump directly from a noncanonical finite object to a canonical one,
  use a shape-specific "badness" complexity that is zero on canonical objects
  and positive on noncanonical ones; this turns canonical dominance into a
  terminating finite-descent step without manufacturing artificial endpoint
  count decreases.
- When source endpoint lemmas naturally produce ordinary policies rather than
  elements of the finite coded domain, add a narrow conversion wrapper from
  those source policies into equal coded representatives.  This keeps the hard
  calculus in source language and avoids forcing every endpoint proof to build
  interval/ray codes manually.
- If the source-facing certificate is proof-valued, avoid packing it under
  `Sigma`; Lean expects a `Type` there and proof-valued structures may live in
  `Prop`.  Use ordinary `Exists` fields for proof-only choices, then `rcases`
  them at the use site.

## Lean Patterns

- If an optimizer proof over functions becomes unwieldy, introduce a finite
  coded feasible type and decode after using `Fintype`.
- Keep objective aliases paper-facing and formula-explicit; push only the
  reusable argmax/ordering theorem into the library.
- When comparing objectives, expose monotonicity as a named field or theorem
  rather than unfolding expectation internals inside every paper wrapper.
- Prefer theorem statements over opaque bundled witnesses in `PaperInterface`;
  bundled certificates are implementation tools and belong in proof files,
  post-paper audit ledgers, or reusable foundation modules.
