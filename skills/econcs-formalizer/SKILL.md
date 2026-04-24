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
  benchmark predicates.
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
- For inequality-heavy proofs, use certificate structures with fields matching
  the exact nonnegativity, strict positivity, and comparison obligations needed
  by the final theorem.
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
- For finite exchange arguments, avoid re-proving whole objective sums by hand.
  Use a generic two-point finite-sum update lemma: if two functions differ only
  at `src` and `dst`, the total sum changes by the two pointwise deltas. Then
  derive first-order inequalities at finite optima from "no profitable
  exchange" rather than restating optimality from scratch.
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
