# EconCSLib Roadmap

## Goal

Turn this repository into a useful Lean library for the
economics-and-computation community by coupling three workstreams:

1. paper formalizations,
2. reusable domain primitives,
3. an agent skill for formalizing new papers.

These should reinforce each other. Papers pressure-test the abstractions, and
the abstractions make later papers and later automation cheaper.

## Current Baseline

This repository is no longer just a fresh scaffold. It now contains one
substantial imported finite/discrete formalization track:

- `DecisionCore/*` for reusable discrete primitives
- `Monoculture/*` for the monoculture paper
- `UserItemFairness/*` for the recommendation-fairness paper
- `AccuracyDiversity/*` for the accuracy-diversity paper

Concrete assets already present:

- reusable `PMF`-based expectation and policy infrastructure,
- finite conditional-expectation helpers,
- classwise/type-symmetric policy lifting,
- finite integer-allocation and representation-share machinery,
- a meaningful monoculture proof path with Mallows theorem seams,
- fairness and accuracy-diversity scaffolds that are more than placeholders,
- a fair-division Test-of-Time path with envy graphs and bounded-envy theorem
  seams,
- a digital-goods auction path with posted-price DSIC/IR/no-positive-transfer
  theorems,
- `HumanStartHere.lean` as a human onboarding file.

This means the next roadmap should build on that imported work rather than
pretend the repository is empty.

## What The Imported Track Changes

The imported track gives this repository:

1. an actual first batch of paper formalizations,
2. a first reusable library nucleus in `DecisionCore`,
3. a concrete continuation plan for one active theorem target,
4. a model for how future papers should be split into shared core and
   paper-specific layers.

So the immediate question is no longer “what should the first paper be?”.
The immediate question is “how do we stabilize and extend the imported track so
it becomes the first durable slice of the broader EconCSLib library?”.

## Active Continuation Target

The main current proof target is still the monoculture/Mallows branch through:

```lean
MallowsComparison.CenterProbabilityCertificate
MallowsComparison.paperHypotheses_of_centerProbabilityCertificate
```

The imported docs indicate the right continuation order:

1. get the imported code building cleanly in this repository,
2. prove the remaining first-choice probability inequalities for the center
   candidate,
3. prove global nonnegativity of the candidatewise summands,
4. instantiate `CenterProbabilityCertificate`,
5. only then move to more ambitious branches.

What not to do yet:

- do not start the Gaussian/Laplacian monoculture branch,
- do not formalize the outer value-vector distribution yet,
- do not refactor the game definitions while trying to close the Mallows path,
- do not start external-solver integration for the fairness LP path yet.

## Working Principles

1. Formalize theorems, not PDFs.
   Work from precise definitions, theorem statements, and proof seams.

2. Every paper must pay library rent.
   Reusable facts should migrate into shared modules rather than stay trapped in
   one paper namespace.

3. Build the skill downstream of real practice.
   The agent skill should be distilled from completed paper passes, not written
   from speculation.

4. Bias toward finite models first.
   The imported track confirms that finite/discrete EC entry points are a good
   first layer.

5. Track theorem seams explicitly.
   The imported monoculture work is valuable because it isolates the exact local
   interface still needing proof.

## Execution Plan

### Milestone 0: Stabilize The Imported Track

Objective: make the imported three-paper track buildable, documented, and
maintainable inside `EconCSLib`.

Tasks:

- finish getting the imported libraries to a clean `lake build`
- keep the imported docs aligned with the code
- document the imported architecture and active proof seams in this repo
- avoid premature renaming or large refactors until the imported code is stable

Exit criteria:

- imported libraries compile in this repository
- the human start path and handoff docs live here, not only in the sister repo

### Milestone 1: Finish The Current Monoculture Seam

Objective: close the next theorem milestone that the imported track was already
aiming at.

Tasks:

- work in the existing Mallows/Kendall/certificate files
- prove the center-candidate first-choice probability inequalities
- prove the required candidatewise nonnegativity facts
- instantiate `CenterProbabilityCertificate`
- use `paperHypotheses_of_centerProbabilityCertificate`

Exit criteria:

- the current Theorem-3-style discrete Mallows milestone is closed
- the imported monoculture branch advances by theorem, not by more scaffolding

### Milestone 2: Consolidate `DecisionCore`

Objective: treat `DecisionCore` as the first serious reusable core of
`EconCSLib`.

Tasks:

- identify which imported primitives are genuinely general
- document what belongs in `DecisionCore` versus paper-specific namespaces
- add missing small lemmas only when demanded by the next paper proof
- start shaping future modules around the imported abstractions rather than
  around a fresh parallel design

Priority abstractions already suggested by the imported work:

- finite expectations under `PMF`
- randomized policies
- finite conditional expectations
- classwise/type-symmetric lifting
- finite allocations and representation shares

Exit criteria:

- new EC papers can reuse `DecisionCore` instead of rebuilding the same finite
  machinery
- repository conventions for shared versus paper-specific code are clearer

### Milestone 3: Advance The Other Two Imported Papers

Objective: turn the user-item fairness and accuracy-diversity scaffolds into
deeper formalizations rather than leaving them one step behind monoculture.

Imported next targets:

- user-item fairness:
  item-side preservation lemmas, fairness-functional preservation, and the LP
  reduction path
- accuracy-diversity (Complete - finite track):
  two-type allocation expansions, exchange lemmas, and the Proposition 2
  square-root homogeneity bridge. The finite Proposition 2 theorem and
  all discrete bounding inequalities are now fully verified. The asymptotic
  sequence topology limit structures remain.

Exit criteria:

- each imported paper gets at least one substantial post-import proof pass
- cross-paper reuse in `DecisionCore` increases

### Milestone 4: Extend Beyond The Imported Track

Objective: use the imported three-paper track as the first batch of examples,
then broaden the library to more classical EC models.

Candidate next areas:

- auctions and mechanism design
- matching and market design
- direct-revelation and incentive-compatibility primitives

The key constraint is that new work should connect to, not bypass, the reusable
finite/discrete core already present.

### Milestone 5: Build The Agent Skill

Objective: once there is enough repo history and enough repeated proof work,
package the formalization workflow into a reusable skill.

The current draft skill lives at
`skills/econcs-formalizer/SKILL.md`. It records the practices that have already
been useful in this repository: stabilize targeted builds first, keep imports
narrow, work from finite/discrete theorem seams, extract shared primitives into
`DecisionCore`, and leave precise handoff notes.

The skill should eventually know how to:

- read a paper summary,
- identify theorem seams,
- separate reusable definitions from paper-local setup,
- propose Lean file decomposition,
- preserve the repo's shared-core versus paper-specific split,
- record assumptions and omitted branches explicitly.

This skill should be downstream of the imported track and at least a few
successful continuation passes.

## Documentation To Keep In Sync

For the imported track, these docs are now important:

- `README.md`
- `docs/START_HERE_FOR_HUMANS.md`
- `docs/DECISION_FAIRNESS_HANDOFF.md`
- `docs/EC_TEST_OF_TIME_FORMALIZATION_PLAN.md`
- `docs/PAPER_MAP.md`
- `docs/ARCHITECTURE.md`
- `HumanStartHere.lean`
- `skills/econcs-formalizer/SKILL.md`

If the active theorem seam changes, update the handoff docs with it.

## Near-Term Backlog

The best immediate sequence from here is:

1. finish a clean build of the imported libraries in this repo,
2. continue the monoculture/Mallows proof where the imported handoff left off,
3. stabilize the `DecisionCore` conventions that the imported papers already
   rely on,
4. then advance the fairness and accuracy-diversity tracks,
5. only after that resume the broader “new paper areas” roadmap.
