# New Contributor Workflow

This guide is for contributors starting from the public `EconCSLib` repository.
It does not assume that you already have a private EconCSLib workspace.

The contribution policy is still provisional. Before starting substantial paper
formalization work, contact Nikhil Garg at ngarg@cornell.edu so the intended
scope, source-paper version, and public/private status are clear.

## 1. Start From The Public Repository

Fork `nikhgarg/EconCSLib` on GitHub, then clone your fork:

```bash
git clone git@github.com:<your-user>/EconCSLib.git
cd EconCSLib
git remote add upstream https://github.com/nikhgarg/EconCSLib.git
git fetch upstream
git checkout main
git merge --ff-only upstream/main
```

Create a branch for one focused contribution:

```bash
git checkout -b <short-topic-name>
```

Keep `upstream/main` as the source of truth for public library code, public
docs, and public paper folders.

## 2. Choose The Contribution Type

Most contributions should fit one of these shapes:

- Reusable library change under `EconCSLib/`.
- Documentation, status, dashboard, or tooling update.
- Improvement to an already-public paper folder under `papers/<PaperName>/`.
- New paper formalization.

Do not mix an unrelated paper formalization with reusable library cleanup in one
pull request unless the library change is needed by that paper and is small
enough to review with it.

## 3. Reusable Library Contributions

Library contributions should be paper-independent. Good examples include
finite-sum lemmas, probability interfaces, optimization certificates, auction
primitives, matching definitions, or theorem wrappers that more than one paper
could reuse.

Before opening a pull request, run the most relevant target. Examples:

```bash
lake build EconCSLib
python3 scripts/audit_repository.py
```

If the full library build is slow, run a narrower target while developing, then
document the command you ran in the pull request.

## 4. Work On An Existing Public Paper

For an existing public paper, start by reading:

- `papers/<PaperName>/README.md`
- `papers/<PaperName>/FINAL_VALIDATION_REPORT.md`
- `papers/<PaperName>/PaperInterface.lean`
- `papers/<PaperName>/DependencyDAG.tex`

Then build the paper target:

```bash
lake build <PaperName>
```

Use `PaperInterface.lean` as the human-facing statement surface. Keep theorem
status, caveats, and dependency-graph styles synchronized when a result moves
from partial or conditional to formalized.

## 5. Start A New Paper

If the paper is intended to be public from the beginning, create a branch from
public `main` and scaffold the paper folder:

```bash
python3 scripts/new_paper.py <paper-url> \
  --folder <CitationStyleFolderName> \
  --title "<Paper Title>" \
  --authors "<Authors>" \
  --version "<Venue or version>"
```

Use the existing folder naming convention, for example `MSVV07AdWords` or
`Roth82StableMatching`.

The first pull request for a new paper can be an intake PR if it contains:

- source version metadata;
- a named-result inventory;
- a dependency DAG scaffold;
- `MainTheorems.lean` and `PaperInterface.lean` placeholders without false
  claims; and
- an honest status table using `docs/STATUS.md`.

Do not mark a result formalized until the corresponding Lean declaration
compiles without `sorry`, `admit`, new unreviewed axioms, or hidden certificate
assumptions.

## 6. If The Paper Is Not Public-Ready

You do not need an existing private EconCSLib repository to start thinking
about a paper. You have three practical options:

- Work locally on a private branch that you do not push anywhere.
- Create your own private repository or private fork, if your GitHub account
  supports that workflow.
- Contact Nikhil to coordinate a private collaboration space.

Do not push unfinished private-sensitive work to a public fork if the source
paper, proof attempts, comments, or intermediate history should not be public.
Public repositories and public forks have public Git history.

When the paper becomes public-ready, open a focused pull request containing only
the approved paper folder, its root `papers/<PaperName>.lean` file, and any
public-safe reusable library changes.

## 7. Pull Request Checklist

Before opening a pull request:

- Rebase or merge from `upstream/main`.
- Run the relevant `lake build` target.
- Keep source PDFs, rendered PDFs, dashboard caches, and local artifacts out of
  Git unless the repository already tracks that artifact type intentionally.
- Update `README.md`, `DependencyDAG.tex`, `PaperInterface.lean`, and
  `FINAL_VALIDATION_REPORT.md` when changing paper-facing status.
- Explain any caveat, source-model assumption, certificate, or proof-route
  deviation in human-facing files.
- Include the exact commands you ran in the pull request description.

For paper formalizations, reviewers should be able to evaluate the claim by
starting from `FINAL_VALIDATION_REPORT.md`, `PaperInterface.lean`,
`DependencyDAG.tex`, and `README.md` without reverse-engineering implementation
proof files.
