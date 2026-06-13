# New Contributor Workflow

This guide is for contributors who want to build on the public `EconCSLib`
repository. It does not assume that you already have a private EconCSLib
workspace.

The contribution policy is still provisional. Before starting substantial paper
formalization work, contact Nikhil Garg at ngarg@cornell.edu so the intended
scope, source-paper version, and public/private status are clear.

Unless explicitly marked otherwise, contributions to the repository's Lean code,
scripts, documentation, and site source are accepted under the Apache License,
Version 2.0. Source-paper PDFs and extracted text caches remain separate
third-party reference artifacts, are not covered by the repository code
license, and should stay out of public commits unless redistribution rights
have been checked separately.

## 1. Use Public Main As A Read-Only Base

Do not work directly on the public repository. Treat
`nikhgarg/EconCSLib/main` as the upstream base that you periodically sync from,
and do the actual development in a private workspace until the contribution is
ready for public review.

Start with a local private clone:

```bash
git clone https://github.com/nikhgarg/EconCSLib.git
cd EconCSLib
git remote add upstream https://github.com/nikhgarg/EconCSLib.git
git fetch upstream
git checkout main
git merge --ff-only upstream/main
```

Then create a local working branch that you do not publish until it is ready:

```bash
git checkout -b <short-topic-name>
```

If you need cloud backup or collaboration before public review, use your own
private repository or coordinate a private collaboration space with Nikhil. A
public fork is not a private workspace.

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
Any paper-facing theorem premise that is not derived in Lean must be an
explicit paper assumption declaration in `Assumptions.lean`, listed in
`status.json` `review_surface.assumption_names`, and checked in
`assumption_match_llm.json` as a true source/model assumption. Hidden
certificate fields, source-row shortcuts, and proof-only hypotheses do not
qualify as fully formalized paper results.
Reusable library theorems may require certificate arguments. That is acceptable
when the certificate is part of the library API, but the paper code must either
construct the certificate from source primitives or keep the paper result
partial/conditional. A paper-facing alias to a certificate-taking library theorem
does not count as a closed paper theorem by itself. Before claiming completion
or opening a public paper PR, run
`python3 scripts/audit_repository.py --library-only --library-premise-audit`; the audit follows
transitive reusable-library dependencies, not just direct aliases.
The default audit also follows paper-local helper chains. A paper-facing row is
not closed if a local helper, or a helper used by that helper, still takes an
unvalidated certificate, source-row equation, proof-only hypothesis, or other
boundary premise. Evidence constructed internally from already proved facts is
discharged; evidence merely consumed by a helper must be visible as a validated
paper assumption or the endpoint remains partial. Do not use `axiom`,
`constant`, `opaque`, or unsafe declarations to bypass this rule.
When `Assumptions.lean` uses `-- audit-premise:` comments, the judge must
validate each exact premise in `assumption_match_llm.json` `premise_judgments`;
approving only the surrounding assumption group is not sufficient. Premises not
explicitly source-matched or already derived in Lean should be marked
`partial_boundary`, and the paper status should remain partial until they are
closed.

## 5. Start A New Paper Privately

New paper formalizations should start in a private workflow, even if the
eventual goal is a public contribution. From a private local clone or private
repository based on public `main`, scaffold the paper folder:

```bash
python3 scripts/new_paper.py <paper-url> \
  --folder <CitationStyleFolderName> \
  --title "<Paper Title>" \
  --authors "<Authors>" \
  --version "<Venue or version>"
```

Use the existing folder naming convention, for example `MSVV07AdWords` or
`Roth82StableMatching`.

The first public pull request for a new paper should contain only public-safe
work. It can be an intake PR if it contains:

- source version metadata;
- a named-result inventory;
- a dependency DAG scaffold;
- `MainTheorems.lean` and `PaperInterface.lean` placeholders without false
  claims; and
- an honest status table using `docs/STATUS.md`.

Do not mark a result formalized until the corresponding Lean declaration
compiles without `sorry`, `admit`, new unreviewed axioms, or hidden certificate
assumptions. If a result still depends on a capacity equation, threshold row,
probability mass formula, external certificate, or witness that the paper does
not explicitly assume, mark the result conditional or partially formalized
until that premise is derived.

## 6. Keep Unfinished Paper Work Private By Default

You do not need an existing private EconCSLib repository to start thinking about
a paper, but unfinished paper work should stay private. Practical options are:

- Work locally on a private branch that you do not push anywhere.
- Create your own private repository or private fork, if your GitHub account
  supports that workflow.
- Contact Nikhil to coordinate a private collaboration space.

Do not push unfinished private-sensitive work to a public fork if the source
paper, proof attempts, comments, or intermediate history should not be public.
Public repositories and public forks have public Git history.

When the paper becomes public-ready, or when the project explicitly decides to
publish a documented partial formalization, publish only a clean review branch
and open a focused pull request containing the approved paper folder, its root
`papers/<PaperName>.lean` file, and any public-safe reusable library changes.

The pull request is the point at which the contribution becomes public. Review
the branch history before opening it.

Public partial formalizations are allowed when the remaining assumption seam is
explicit and useful for public review or collaboration. That should be an
intentional project decision, not the default for new paper work.

## 7. Pull Request Checklist

Before opening a pull request:

- Rebase or merge from `upstream/main`.
- Run the relevant `lake build` target.
- Push only a public-safe review branch or fork after the work is ready for
  review.
- Keep source PDFs, dashboard caches, and local artifacts out of Git unless the
  repository already tracks that artifact type intentionally.
- Update `README.md`, `DependencyDAG.tex`, `DependencyDAG.pdf`,
  `PaperInterface.lean`, `status.json`, and `FINAL_VALIDATION_REPORT.md` when
  changing paper-facing status.
- Run `python3 scripts/sync_paper_status.py` after editing a paper-local
  `status.json`; it refreshes the aggregate JSON, docs table, README table, and
  site table. Include the generated status files in the pull request.
- Explain any caveat, source-model assumption, certificate, or proof-route
  deviation in human-facing files.
- Include the exact commands you ran in the pull request description.

For paper formalizations, reviewers should be able to evaluate the claim by
starting from `FINAL_VALIDATION_REPORT.md`, `PaperInterface.lean`,
`DependencyDAG.tex`, and `README.md` without reverse-engineering implementation
proof files.
