# EconCSLib Roadmap

## Vision

EconCSLib aims to become a reusable Lean 4 library and audit trail for
Economics and Computation. The repository separates paper-independent EC
mathematics under `EconCSLib/` from source-faithful paper formalizations under
`papers/`.

## Phase 1: Public Release Hardening

- Keep `lake build EconCSLib` green on every public commit.
- Keep each public paper folder reviewable from `FINAL_VALIDATION_REPORT.md`,
  `PaperInterface.lean`, `DependencyDAG.tex`, and `README.md`.
- Keep the top-level README concise and route detailed paper status to
  `docs/PAPER_STATUS.md` and paper-local ledgers.
- Publish additional paper formalizations only once their paper-facing ledger
  and validation report are ready for public review.

## Phase 2: Reusable EC Library Growth

Upstream reusable facts when they pass the second-paper test: a definition,
lemma, theorem interface, or proof pattern should move into `EconCSLib/` when
it is likely to support more than one paper.

Current high-value areas:

- finite sums, inequalities, and asymptotic helpers;
- finite and continuous probability primitives;
- matching markets and stability;
- mechanism-design interfaces for auctions and incentives;
- online algorithms and competitive-analysis certificates;
- fair-division primitives; and
- recommender-system and fairness models.

## Phase 3: Paper Contribution Pipeline

The public workflow should make it straightforward for contributors to develop
paper formalizations privately and submit them when complete. A public paper
contribution should include a compact `PaperInterface.lean`, a theorem-status
ledger, a dependency DAG, a validation report, and a reproducible build target.

Partially verified papers may remain in private repositories until their
authors are ready to publish them. When a paper becomes public-ready, its
paper-local history can be imported with filtered history rather than exposing
unrelated unfinished work.

## Phase 4: Agent-Assisted Formalization

EconCSLib also serves as a testbed for AI-assisted formalization workflows.
The `skills/econcs-formalizer/` bundle records reusable instructions and proof
patterns for agents that ingest a source paper, build a theorem inventory,
identify reusable library seams, and produce Lean code plus human-review
artifacts.
