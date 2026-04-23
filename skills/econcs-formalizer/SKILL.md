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

4. Extract shared primitives.
   Reusable finite expectations, policies, allocations, valuations, mechanisms,
   rankings, conditional expectations, and sign lemmas should live in shared
   modules. Keep only paper-specific definitions in paper namespaces.

5. Make every paper pay library rent.
   When a proof needs a reusable object, add the general version once and reuse
   it. Avoid parallel versions of allocations, randomized policies, mechanisms,
   or expectations in each paper folder.

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
- Online algorithms: separate histories, feasible irrevocable actions,
  objective value, benchmark/offline optimum, and competitive-ratio statements.
- Social choice/rankings: use finite rankings/permutations, first/second choice
  accessors, pairwise comparisons, and voting-rule interfaces before hardness
  reductions.

## Theorem-Seam Patterns

- For constructive paper proofs, formalize local invariants first, then assemble
  the main theorem by induction or finite recursion.
- For proofs whose hard part is a known paper lemma, package the lemma as a
  named predicate or certificate and prove the surrounding algebra/induction
  unconditionally.
- For inequality-heavy proofs, use certificate structures with fields matching
  the exact nonnegativity, strict positivity, and comparison obligations needed
  by the final theorem.
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
