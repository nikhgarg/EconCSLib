---
name: econcs-formalizer
description: Formalize economics-and-computation papers in Lean. Use when asked to add, continue, triage, or plan Lean formalizations of EC/ACM EC/SIGecom-style papers; extract reusable finite/discrete primitives; choose theorem seams; repair Lean/mathlib proof scripts; or prepare general handoff guidance for future formalization work.
---

# EconCS Formalizer

Use this skill to turn economics-and-computation papers into maintainable Lean
code. Keep repository-specific status out of this file; in `EconCSLean`, that
belongs in `docs/ECONCSLEAN_CURRENT_STATUS.md`.

## Core Rule

Formalize theorem seams, not PDFs. Start from the paper's precise definitions,
the main result to be checked, and the smallest reusable lemmas needed to close
that result.

## Library Layering Rule

Put generic EC/CS/econ results in the main EconCS library, then make paper
folders mostly apply those results.

- Main library modules should own reusable primitives, definitions, and theorems:
  allocations, valuations, mechanisms, rankings, PMFs, finite expectations,
  graph/path lemmas, sign lemmas, certificate interfaces, and generic algorithm
  correctness patterns.
- Paper-specific folders should mainly translate paper notation into the shared
  primitives, instantiate assumptions, prove genuinely paper-local lemmas, and
  state the paper-facing theorem.
- If two papers could use a lemma after renaming variables, it belongs in the
  generic library first. Do not let reusable results accumulate inside a paper
  namespace just because that is where they were discovered.
- If a proof starts with a paper-local lemma and it becomes generic, extract it
  before building more paper-specific code on top of it.
- Paper folders may keep thin wrappers with paper names, but those wrappers
  should usually call generic theorems rather than duplicate their proofs.

## Paper Folder Contract

Each paper-specific folder should be auditable by a human who wants to compare
the Lean statements against the paper.

- Record the exact paper source version in the folder. Prefer a folder
  `README.md` with the arXiv/ACM/official URL, title, authors, venue/version,
  and access date. If the project policy allows PDFs, keep the paper PDF there;
  otherwise do not commit the PDF and make the README link to the exact version
  being formalized.
- Add one central Lean file for paper-facing theorem statements, conventionally
  named `MainTheorems.lean`, `PaperTheorems.lean`, or the existing paper root if
  the folder already has a root module. This file should state and prove only
  the main theorem wrappers and import the detailed proof files.
- Main theorem definitions/functions in that central file should mirror the
  paper statement closely enough that a human can inspect just this file and
  verify the intended theorem was formalized. Use paper theorem numbers/names in
  docstrings and keep wrappers thin.
- Add a structured folder `README.md` theorem-status table with columns like:
  paper theorem/definition, Lean declaration, status (`formalized`,
  `conditional`, `scaffold`, `not started`), file, and remaining assumptions.
- If a theorem is only conditional, the README must name the exact certificate
  or assumption declaration that remains. Do not describe it vaguely as
  "technical details".
- Detailed lemmas may live in many files, but the central theorem file should be
  the stable public interface for that paper.

## Workflow

1. Orient before editing.
   Read the repo README, roadmap, architecture notes, and paper-specific
   handoff documents. Identify the public theorem target and the smallest local
   lemma that moves it forward.

2. Stabilize the build first.
   Run targeted `lake build <module>` commands before making broad changes. Fix
   dependency, import, or cache problems before interpreting downstream proof
   errors.

3. Choose finite/discrete models first.
   EC papers often have useful finite entry points: finite agents, items,
   actions, rankings, allocations, mechanisms, PMFs, and finite sums. Formalize
   those before attempting asymptotic, measure-theoretic, or complexity-heavy
   layers.

4. Extract shared primitives into the main library.
   Reusable finite expectations, policies, allocations, valuations, mechanisms,
   rankings, conditional expectations, graph lemmas, and sign lemmas should live
   in main library modules, not buried in one paper folder. Keep only
   paper-specific definitions and wrappers in paper namespaces.

5. Make every paper pay library rent.
   When a proof needs a reusable object, add the general version once and reuse
   it. Avoid parallel versions of allocations, randomized policies, mechanisms,
   expectations, graph reachability, or inequality certificates in each paper
   folder.

6. Prefer compileable partial progress.
   If the full main theorem is not ready, add definitions, local invariants,
   certificate structures, and conditional theorems that compile. Avoid `sorry`
   unless the user explicitly asks for placeholder theorem statements.

7. Document exact theorem seams.
   When stopping mid-proof, record the module, theorem, assumptions still
   missing, commands run, and the next lemma to prove. Future agents should not
   have to rediscover the proof state.

8. Verify narrowly, then broadly.
   First build the touched module. Then build the parent paper root. Run full
   `lake build` for release/integration checks.

9. For author-wide paper campaigns, maintain a running markdown report.
   Record every paper screened, the source version, venue, author-position
   decision, theorem-status decision, declarations added, blocker if any, build
   command, and commit hash. Do not advance from a paper until either its main
   theorem interface is closed without `sorry`/conditional assumptions or the
   report states the precise bug/too-hard reason blocking faithful
   formalization.

## External Library Reconnaissance

Before implementing substantial probability, statistics, or learning-theory
machinery from scratch, check whether existing Lean libraries already contain
the needed theorem and whether their Lean/mathlib versions are compatible.

- Statistical learning theory: `YuanheZ/lean-stat-learning-theory`
  (`SLT/*`) formalizes empirical-process infrastructure, covering numbers,
  metric entropy, sub-Gaussian processes, Gaussian concentration, Efron-Stein,
  Dudley's entropy integral, and least-squares regression bounds. Useful module
  names include `SLT.CoveringNumber`, `SLT.MetricEntropy`, `SLT.SubGaussian`,
  `SLT.Dudley`, `SLT.EfronStein`, `SLT.GaussianLipConcen`, and
  `SLT.LeastSquares.*`.
- Related probability sources referenced by that project include
  `auto-res/lean-rademacher` for Rademacher/Dudley material and
  `RemyDegenne/CLT` for characteristic-function/CLT infrastructure.
- Optimization and convex analysis: `optsuite/optlib` (`Optlib/*`) formalizes
  convex functions, subgradients, Farkas-style alternatives, weak duality, KKT
  conditions, and convergence of standard first-order optimization algorithms.
  It is the first external place to inspect before building convex-optimization
  or LP-duality infrastructure for recommendation, market, and admissions
  papers.
- Do not add one of these as a dependency blindly. First inspect
  `lean-toolchain`, `lakefile`, and `lake-manifest`; if the toolchain is behind
  the current repo, either port only the needed lemmas into a local generic
  module with attribution or isolate a compatibility branch.
- Prefer using upstream theorem names as search terms. If porting, preserve the
  conceptual interface but adapt notation/imports to the local library layer.

## Modeling Heuristics

- Fair division: start with finite bundles, allocations, monotone valuations,
  envy, EF/EF1-style predicates, envy graphs, and local preservation lemmas.
- Auctions/mechanisms: separate reports, outcomes, allocations, payments,
  utility, truthfulness, individual rationality, revenue, and approximation or
  benchmark predicates. For auction Test-of-Time tracks, start with finite
  certificate interfaces: fixed-price benchmarks for digital goods, explicit
  position outcomes before sorted GSP mechanisms, and bundle-allocation
  feasibility before greedy combinatorial-auction algorithms.
- Matching: separate preferences, feasibility, matching, blocking pairs,
  stability, deferred acceptance, and strategic-report predicates.
- Games/learning: separate finite games, mixed distributions, payoffs,
  equilibrium predicates, regret/calibration, and empirical distributions.
- Statistical learning/probability: before building custom measure-theoretic
  probability, look for reusable concentration, sub-Gaussian, covering-number,
  entropy, empirical-process, and regression results in SLT-style libraries;
  when toolchain mismatch prevents direct import, port narrowly into generic
  EconCS probability/statistics modules.
- Online algorithms: separate histories, feasible irrevocable actions,
  objective value, benchmark/offline optimum, and competitive-ratio statements.
  For AdWords/MSVV, first close the finite offline benchmark and LP weak-duality
  layer: assignments, spend, revenue, budget feasibility, residual budget,
  feasible next-query assignment, offline optimum, fractional LP feasibility,
  integral-to-fractional embedding, dual feasibility, and dual objective. Then
  model Balance/MSVV as a history fold whose local step chooses
  a feasible advertiser maximizing the scaled bid
  `bid * (1 - exp(spentFraction - 1))`; prove run feasibility separately from
  the competitive-ratio invariant. Under small bids, prove the boundary lemma
  that a blocked advertiser has spent fraction strictly above `1 - ε`; this is
  the finite replacement for repeatedly handwaving away exhausted advertisers.
  Also expose the dual-cover proof through slack scores:
  `bid * (1 - alpha) ≤ beta` implies the LP dual constraint
  `bid ≤ bid * alpha + beta`; this is the bridge from Balance choices to
  `DualFeasible`. For finite advertiser sets, define max-slack query duals and
  assignment-induced MSVV advertiser duals from spent fractions, then prove they
  are dual-feasible before trying to prove the global scaled dual-objective
  bound. Package that last finite charging argument as a named objective-bound
  certificate so the paper-facing `1 - 1/e` theorem remains a thin wrapper.
  Before attacking the objective bound, prove run monotonicity: spend, spent
  fractions, and assignment-induced MSVV dual alphas only increase along a
  feasible online history. This yields the key comparison that final slack
  scores are bounded by earlier Balance scores. Use that comparison with the
  Balance maximizer to close the non-exhausted-query beta charge; handle
  exhausted advertisers separately with the small-bids boundary lemma by first
  proving a final-alpha lower bound `exp (-ε)` and then a final-slack bound
  `bid * (1 - exp (-ε))`. For finite max-slack query duals, package the mixed
  query charge in a summation-friendly form: chosen Balance score plus an
  explicit max-bid small-bids error term.
- Social choice/rankings: use finite rankings/permutations, first/second choice
  accessors, pairwise comparisons, and voting-rule interfaces before hardness
  reductions.

## Theorem-Seam Patterns

- For constructive paper proofs, formalize local invariants first, then assemble
  the main theorem by induction or finite recursion.
- For finite deterministic-rule optimization statements, first prove a generic
  maximizer-existence theorem over the finite function type `(instances →
  actions)`. Then keep paper folders responsible only for defining the
  paper-specific real-valued objective and applying the generic existence
  result.
- For proofs whose hard part is a known paper lemma, package the lemma as a
  named predicate or certificate and prove the surrounding algebra/induction
  unconditionally.
- For posted-price and prior-free digital-goods auctions, prove truthfulness at
  the threshold-rule level: if the threshold offered to bidder `i` is
  independent of `i`'s own report, accepting iff bid exceeds that threshold is
  DSIC. Then instantiate random-sampling or market-price auctions by proving
  the relevant own-bid-independence lemma. For fixed-price benchmarks, define a
  finite bidder-value candidate benchmark early; the remaining paper lemma is
  then the reduction from arbitrary feasible prices to bidder-value prices.
  For random-sampling digital-goods auctions, first prove the deterministic
  cross-sample threshold mechanism truthful for an arbitrary fixed partition;
  only after that add probability over partitions and revenue approximation.
  The fixed-price benchmark reduction should use the minimum accepted bidder
  value: raising a feasible price to that value preserves the sale count lower
  bound and weakly increases revenue.
  Use a nonnegative offer-price wrapper around finite candidate prices so
  no-positive-transfer and expected-revenue nonnegativity proofs do not inherit
  infeasible negative candidate values from empty samples.
  When the approximation proof is too large for the current pass, package it as
  a named certificate whose statement is exactly the benchmark/revenue
  inequality needed by the paper-facing theorem.
- For GSP/position-auction work, first formalize `PositionOutcome` with
  per-click payments, utility, revenue, welfare, and feasibility. A concrete
  non-truthfulness witness is a good first theorem before building a generic
  bid-sorting mechanism and equilibrium comparisons. Use local envy-freeness as
  an outcome-level certificate for "no profitable assigned-slot deviation"
  before trying to prove full Nash equilibrium of a sorted GSP mechanism.
- For combinatorial auctions, reuse the fair-division bundle/allocation layer.
  Keep feasibility separate from direct mechanisms because approximation
  algorithms may leave goods unallocated. For single-minded bidders, define the
  bundle-containment valuation before proving greedy allocation or
  critical-value payment theorems. Prove pairwise-disjoint accepted-set
  feasibility separately from greedy optimality; this lets the greedy algorithm
  theorem focus on its acceptance invariant and critical-price monotonicity.
- For inequality-heavy proofs, use certificate structures with fields matching
  the exact nonnegativity, strict positivity, and comparison obligations needed
  by the final theorem.
- For finite rounding arguments, split the proof into reusable layers: a
  generic no-crossing combinatorial theorem, a paper-specific exchange
  certificate that rules out crossings at optima, and a final triangle
  inequality step converting anchor closeness plus rounding closeness into the
  paper's approximation guarantee. If the paper proof uses floor/ceiling
  thresholds around a real optimum, use separate lower and upper anchors rather
  than forcing one integer anchor to play both roles. For separable objectives
  with square-root first-order conditions, discharge abstract exchange
  certificates by proving likelihoods are a positive scale times squared
  shifted targets and that anchors bracket those shifted targets.
- When a paper proof derives a continuous relaxation by Lagrange multipliers,
  verify the normalization algebra before encoding the theorem. Off-by-`m`
  shifts can appear when the derivative depends on `x_t + 1`; keep the theorem
  conditional or log a proof-audit note until the exact discrete rounding bound
  is recovered.
- For LP sparsity results, separate the linear-programming theorem from the
  finite counting consequence. First encode the active-support bound supplied
  by basic feasible solutions, then prove reusable counting lemmas such as:
  if every item has an active type and total active type-item pairs are at most
  `n + K - 1`, then at most `K - 1` items can be shared by multiple types.
  For normalized min-item-fairness objectives, positive item fairness usually
  discharges the "every item active" side condition: if an item has no positive
  support, its raw and normalized item utility are zero, contradicting a
  strictly positive finite minimum. Keep the remaining LP/BFS active-support
  theorem as the separate hard seam.
  To prove the paper's `IF* > 0` lemma, use the uniform finite PMF as an
  explicit witness: with strictly positive weights/utilities every item has
  positive raw and normalized utility under the uniform policy, so the finite
  minimum is positive and `sSup` is positive once attainable values are bounded
  above by one.
- For strict monotonicity claims, check boundary cases before proving the
  general theorem. Bernoulli/probability variance terms often become
  identically zero at `q = 0` or `q = 1`, so a paper statement that says
  "strictly decreasing" may need an explicit interior assumption. Also prove
  the corresponding weak monotonicity theorem on the closed interval when it is
  true; that is usually the paper-safe replacement.
- Prefer sum-level certificates when the theorem is about a total expectation
  or finite sum. Do not impose candidatewise nonnegativity merely because it
  would make a `sum_univ_pos_of_pos_of_nonneg` proof convenient; in ranking and
  Mallows-style arguments, non-center fibers can have negative gap mass even
  when the total theorem is true.
- For Mallows/ranking proofs, match the paper's pairwise decomposition when the
  argument compares `(i,j)` and `(j,i)` top-two events. First prove the exact
  top-two expansion of the finite sum, then define the ordered-pair term and
  prove the antisymmetric swap identity. Discharge the remaining proof through
  bracket inequalities for `(i,j)` plus `(j,i)`. This is safer than forcing
  first-choice fiber signs.
- When clearing positive probability denominators, expose the unnormalised
  numerator as a reusable definition and prove an equality from the normalized
  expectation to numerator divided by a positive denominator. Also prove the
  positivity equivalence in both directions, so later certificate interfaces can
  move freely between normalized probabilities and denominator-cleared finite
  sums.
- For AdWords and generalized online matching, use the LP-duality theorem seam
  before attempting the full `1 - 1/e` proof. Prove weak duality once from
  `DualFeasible`, then package the algorithm analysis as a
  `PrimalDualCompetitiveCertificate` with fields for primal feasibility,
  nonnegative ratio, dual variables, dual feasibility, and the scaled
  dual-objective bound. The remaining Balance/MSVV work should construct that
  certificate from the query-history fold; run feasibility should already be
  closed through a generic `ChoiceRuleFeasible` theorem. The small-bids limit
  should be a separate paper-local theorem, not mixed into the finite LP layer.
- For symmetry/type-reduction arguments, prove the generic fiber facts first:
  weighted sums by type-cardinality equal sums over original agents, and finite
  minima over agents equal finite minima over types when representatives witness
  every fiber. Then paper reductions become mostly rewriting. For optimization
  reductions, separate exact functional preservation from supremum reasoning:
  first prove lift/descend preservation, then prove symmetrization dominance
  (same item feasibility and weakly better objective), then prove the `sSup`
  equality from explicit nonempty/bounded-above feasible-value side conditions.
  Avoid opaque assumptions such as "the optimal values are equal" when they can
  be replaced by this order-theoretic reduction.
- For normalized utility objectives, prove boundedness before attempting
  compactness. A finite PMF expectation of row utilities is at most the finite
  row maximum, so positive normalizers usually give normalized utility `≤ 1`
  and immediately discharge `BddAbove` obligations for feasible value sets.
- For baseline constrained problems with constraint level `γ = 0`, first check
  whether the constraint reduces to nonnegativity. If objectives are normalized
  nonnegative utilities, prove each normalized coordinate is nonnegative, take a
  finite-minimum nonnegativity lemma, and witness nonemptiness with an arbitrary
  default policy. In type-reduction models, transfer nonnegative utilities
  through representatives and nonnegative type weights through fiber
  cardinalities.
- For finite exchange arguments, avoid re-proving whole objective sums by hand.
  Use a generic two-point finite-sum update lemma: if two functions differ only
  at `src` and `dst`, the total sum changes by the two pointwise deltas. Then
  derive first-order inequalities at finite optima from "no profitable
  exchange" rather than restating optimality from scratch.
- For recommendation diversity/homogeneity papers, split the proof into three
  layers. First prove finite exchange or first-order conditions that force
  pairwise count balance. Then prove a generic representation lemma converting
  count error, such as `|count t - N / T| <= 1`, into share error, such as
  `1 / N`, for the paper's `gamma`-homogeneity profile. Only then attack the
  asymptotic/order-statistic layer. For symmetric i.i.d. Bernoulli items, the
  finite balance proof should cancel the common positive likelihood-success
  coefficient and use strict antitonicity of `(1 - q)^k` when `0 < q < 1`.
  For uniform `[0,1]`, `k = 1` recommendation values, use the closed form
  `1 - 1 / (q + 1)` for the expected maximum of `q` samples. Its forward
  marginal is `1 / ((q + 1) * (q + 2))`, and its positive-count backward
  marginal is `1 / (q * (q + 1))`. Proposition-style square-root homogeneity
  should be separated into: exact marginal algebra, a square-root target-profile
  representation bridge, and then the real-relaxation/integer-rounding theorem.
  For rounding lemmas, first isolate the generic combinatorial fact: if an
  integer vector has no high/low crossing around integer anchors and the anchor
  total is within one type-cardinality of the target total, then every count is
  within one type-cardinality of its anchor. The paper-specific analytic work is
  proving that optimality of the separable objective rules out the crossing. A
  useful intermediate certificate is a strict boundary exchange comparison:
  the loss from removing a high-anchor item is strictly smaller than the gain
  from adding a low-anchor item, uniformly over high/low pairs.
- For finite fair-division allocation theorems, first prove the theorem for an
  abstract marginal bound. Then add a paper-facing corollary instantiating the
  bound as the finite maximum one-good marginal value.
- For finite fixed-total count-allocation optimization, encode feasible
  allocations as functions into `Fin (N + 1)` plus a total-sum proof. Optimize
  over that finite code space, then decode back to the paper allocation type.
  This is often enough to discharge "there exists an optimum" seams before
  invoking exchange or first-order conditions.
- For algorithmic statements, separate the existence/correctness theorem from
  runtime or complexity claims unless the complexity layer is already in scope.
- When a theorem is conditional, name the remaining seam mathematically, not as
  an implementation excuse. Good names describe the paper lemma being assumed.

## Lean Proof Patterns

- For finite singleton indicator sums, use:

```lean
simpa using
  (Finset.sum_ite_eq' Finset.univ key
    (fun _ => weight))
```

- For sums of divisions in real-valued finite sums, import
  `Mathlib.Algebra.BigOperators.Field` and use `Finset.sum_div`.
- For `PMF` over finite types, prefer existing finite-expectation lemmas and
  `pmfExp`/`pmfProb` abstractions over hand-expanding `PMF` internals.
- For pure PMF cases, use lemmas such as `pmfExp_pure`,
  `pmfPairExp_pure_left`, and `pmfPairExp_pure_right` when available.
- When a proof branches on an abbreviation but the goal expands it, normalize
  with local facts:

```lean
have h' : c = rawExpr := by simpa [abbrevName] using h
```

- For pair events, convert each component explicitly:

```lean
have hc : c = rawFirst := by simpa [firstAbbrev] using h.1
have hd : d = rawSecond := by simpa [secondAbbrev] using h.2
```

- To transport hypotheses across equality of reference structures, rewrite the
  reference explicitly rather than hoping `simp` finds it.
- Mark definitions `noncomputable` when they depend on real comparisons,
  filtered finite sets over propositions, `PMF` normalization, or classical
  choice.
- Keep imports narrow. Prefer specific Mathlib modules over `import Mathlib` in
  new or actively repaired files.

## Build Hygiene

- Lake reuses `.olean` artifacts when sources, imports, Lean version, and
  dependency artifacts are unchanged.
- After changing `lean-toolchain`, `lakefile.toml`, or dependency revisions,
  expect substantial rebuilds.
- If generated artifacts produce invalid headers or impossible import errors,
  clean generated dependency outputs and rebuild rather than patching random
  downstream files.
- If a long build is interrupted, already-finished modules usually remain
  cached; rerunning resumes from remaining work.
- Do not infer that downstream files are broken until the direct imported module
  builds.
- Existing warnings are not build failures unless the user asks for lint cleanup
  or the project enforces warning-free builds.
- If build logs are dominated by repeated non-actionable linter warnings,
  quiet only those specific style/noise linters in `lakefile.toml`; do not
  disable proof checking or hide theorem errors.
- To save context during iteration, redirect targeted builds to a temporary log
  and print only the tail on failure or completion, e.g.:

```bash
lake build UserItemFairness.MainTheorems >/tmp/econcs-build.log 2>&1
status=$?
tail -80 /tmp/econcs-build.log
exit $status
```

- Prefer `lake build <touched-root-module>` over full `lake build` until the
  paper slice is ready for integration.

## Paper Triage

Prefer first-pass formalizations with:

- finite objects and finite sums,
- constructive algorithms with simple invariants,
- clean equilibrium, allocation, matching, ranking, or auction definitions,
- reusable primitives likely to help later papers,
- theorem statements decomposable into local lemmas.

Defer or isolate papers whose first main result depends on:

- large complexity-theory reductions,
- heavy measure theory or asymptotics,
- external solvers without certificate interfaces,
- long empirical pipelines,
- broad economic existence theorems before the finite library is mature.

## Handoff Checklist

Before ending work, update a repo note or paper handoff with:

- build commands that passed or failed,
- active theorem seam,
- assumptions imported from the paper,
- shared abstractions added,
- next lemma a future agent should prove.
