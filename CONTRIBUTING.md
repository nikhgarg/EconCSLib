# Contributing to EconCSLib

Draft policy: this contribution process is provisional while EconCSLib is being
prepared for public release. If you want to contribute, please contact Nikhil
Garg at ngarg@cornell.edu before starting substantial work.

EconCSLib has two connected goals:

- maintain a reusable Lean library for economics and computation; and
- maintain source-faithful, auditable formalizations of individual papers.

The public repository should contain reusable library code, tooling, docs, and
completed paper formalizations. Partially formalized papers may be developed in
private workspaces until their authors are ready to make them public.

## What To Contribute

Contributions are welcome in two main categories.

### Reusable Library Updates

Library contributions belong under `EconCSLib/`. These should be
paper-independent definitions, lemmas, theorem interfaces, or proof tools that
could plausibly be reused by more than one economics-and-computation
formalization.

Good candidates include probability primitives, optimization certificates,
matching and auction abstractions, finite expectation lemmas, stochastic-process
tools, asymptotic helpers, and reusable theorem wrappers.

Library pull requests may be submitted before the motivating paper
formalization is public, provided the contribution is self-contained and does
not reveal private or unfinished paper material.

### Completed Paper Formalizations

Paper contributions belong under `papers/<PaperName>/`, where `<PaperName>`
uses the existing citation-style convention, for example
`MSVV07AdWords` or `Roth82StableMatching`.

A completed paper contribution should include:

- `README.md`
- `FORMALIZATION_PLAN.md`
- `DependencyDAG.tex`
- `MainTheorems.lean`
- `PaperInterface.lean`
- any needed implementation modules
- a validation summary or `FINAL_VALIDATION_REPORT.md`
- a passing Lean build target for the paper

`PaperInterface.lean` should be the compact human-facing surface: source
definitions and named theorem statements in paper order. Put broad proof
plumbing, helper endpoints, and implementation detail in `MainTheorems.lean`,
`ProofInterface.lean`, or lower paper-local modules.

## Private Workflows For Unfinished Papers

If a paper is not ready to be public, develop it in a private repository or
private clone. Keep the full working history there.

When the paper is complete, publish only the paper folder and any reusable
library updates that are ready for public review. If you want to preserve
development history, prefer a private repository dedicated to that paper. That
makes it possible to publish a filtered or subtree history later without
exposing unrelated unfinished work.

Do not rely on a private branch inside the public repository to hide unfinished
work. Public GitHub repositories do not provide private per-branch visibility,
and public forks are public.

## Pull Request Expectations

Before opening a pull request:

- keep imports as narrow as practical;
- avoid `sorry`, `admit`, new top-level `axiom`s, or `unsafe` declarations;
- run the relevant targeted `lake build` command;
- update the paper README, dependency DAG, and validation notes when changing a
  paper-facing theorem status;
- keep source-paper caveats and additional assumptions explicit in theorem
  statements and ledgers; and
- avoid mixing unrelated paper work into a library PR.

For reusable library changes, a typical validation command is:

```bash
lake build EconCSLib.Foundations
python3 scripts/audit_repository.py
```

For paper changes, build the paper target, for example:

```bash
lake build Roth82StableMatching
```

The full target is desirable before release-oriented merges:

```bash
lake build EconCSLib
```

## Pull Request Checklist

- [ ] This pull request is either a reusable-library change or one completed
      paper formalization.
- [ ] `lake build <target>` passes for the changed library or paper.
- [ ] Paper theorem-status rows use the vocabulary in `docs/STATUS.md`.
- [ ] `PaperInterface.lean` exposes the human-facing theorem statements.
- [ ] Caveats and source-proof deviations are documented in the paper README or
      `FINAL_VALIDATION_REPORT.md`.
- [ ] Source PDFs, rendered local PDFs, dashboard caches, and other ignored
      local artifacts are not added to Git.

## Review Standard

Lean verifies proofs relative to the formal statements, imports, and
assumptions. Human review is still required to check that the Lean statements
faithfully represent the source paper.

For paper formalizations, reviewers should be able to start from:

1. `FINAL_VALIDATION_REPORT.md` or the validation summary;
2. `PaperInterface.lean`;
3. `DependencyDAG.tex`; and
4. `README.md`.

If those files do not clearly state what was proved and what assumptions
remain, the paper contribution is not ready to merge.
