# EconCSLib Documentation

This directory has two kinds of documentation.

## Human-Facing

These files are for readers who want to understand the project, paper status,
or what a completed formalization proves without reading proof internals.

- [../README.md](../README.md): short project overview and review path.
- [REVIEW_DASHBOARD.md](REVIEW_DASHBOARD.md): theorem-statement review
  dashboard workflow.
- [PAPER_STATUS.md](PAPER_STATUS.md): public paper citation, build target,
  status, caveat, and review entrypoint.
- [PUBLIC_REPOSITORY_WORKFLOW.md](PUBLIC_REPOSITORY_WORKFLOW.md): public/private
  repository split, completed-paper imports, and private partial-paper policy.
- [PUBLIC_RELEASE_CHECKLIST.md](PUBLIC_RELEASE_CHECKLIST.md): checks before a
  public announcement or broad external contribution request.
- [REPOSITORY_LAUNCH_PLAN.md](REPOSITORY_LAUNCH_PLAN.md): current launch plan
  for the public/private split and Pages activation.
- [PAGES_PUBLISHING.md](PAGES_PUBLISHING.md): static-site publishing steps for
  GitHub Pages.
- Paper-level `FINAL_VALIDATION_REPORT.md`, `PaperInterface.lean`, and
  `DependencyDAG.pdf` files under `papers/<PaperName>/`.

## Agent And Maintainer-Facing

These files are operational references for formalization agents and maintainers.
They may assume Lean familiarity and may be more detailed.

- [AGENT_FORMALIZATION_WORKFLOW.md](AGENT_FORMALIZATION_WORKFLOW.md): how to
  start, run, audit, and finish a paper formalization with an agent.
- [ARCHITECTURE.md](ARCHITECTURE.md): repository structure, paper-folder
  contract, paper-facing ledger rules, and maintenance notes.
- [ECONCSLIB_DOMAIN_INDEX.md](ECONCSLIB_DOMAIN_INDEX.md): reusable library
  modules by domain.
- [LEAN_STYLE.md](LEAN_STYLE.md): Lean style conventions.
- [STATUS.md](STATUS.md): controlled vocabulary for paper status rows.
- [THEOREM_ERGONOMICS.md](THEOREM_ERGONOMICS.md): theorem statement and
  interface conventions.
- [PROBABILITY_LIBRARY_ROADMAP.md](PROBABILITY_LIBRARY_ROADMAP.md) and
  [OPTIMIZATION_LIBRARY_ROADMAP.md](OPTIMIZATION_LIBRARY_ROADMAP.md): reusable
  library roadmaps.

Detailed proof-strategy rules for agents live in
[`skills/econcs-formalizer/`](../skills/econcs-formalizer/).
