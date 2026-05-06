# EconCSLib

EconCSLib is a Lean 4 project for checking results in Economics and
Computation. The repository has two roles:

- Build a reusable library of mathematical tools for EC: probability,
  optimization, matching, auctions, online algorithms, fair division, learning,
  and related foundations.
- Keep a paper-by-paper audit trail showing which source definitions and
  theorems have been formalized, which assumptions remain, and where the proof
  deviates from an informal paper argument.

The project is meant to support both formalization work and human review. A
human reader should be able to open a completed paper folder and understand
what was proved without reading the full Lean implementation.

## How The Repository Is Organized

- `EconCSLib/` is the reusable library. Code here should be paper-independent
  and useful across more than one formalization.
- `papers/` contains one folder per source paper. These folders preserve the
  paper's notation, theorem numbering, proof DAG, validation report, and
  human-facing Lean interface.
- `docs/` contains project documentation. Some files are human-facing strategy
  and status documents; others are detailed conventions for agents and
  maintainers.
- `skills/econcs-formalizer/` contains the agent workflow instructions used to
  formalize papers consistently.

## Reviewing A Formalized Paper

Start in the paper folder under `papers/<PaperName>/`.

For a completed or nearly completed paper, read these files in this order:

1. `FINAL_VALIDATION_REPORT.md`: source checked, theorem inventory, proof
   deviations, remaining assumptions, and final status.
2. `PaperInterface.lean`: readable definitions and theorem statements matching
   the paper. This is the main human-facing Lean file.
3. `DependencyDAG.pdf`: visual map of named definitions, lemmas, theorems, and
   remaining caveats.
4. `README.md`: paper metadata and theorem-status ledger.

Implementation files such as `MainTheorems.lean` and lower proof files are for
maintainers and agents. They should not be necessary for a first human audit of
what the paper claims and what Lean proves.

## Current Status

Paper status changes frequently. Use:

- [docs/ECONCSLEAN_CURRENT_STATUS.md](docs/ECONCSLEAN_CURRENT_STATUS.md) for the
  current project status ledger.
- Individual `papers/<PaperName>/README.md` files for paper-specific caveats.
  for the author-paper formalization summary.

## Starting A New Paper With An Agent

Use [docs/AGENT_FORMALIZATION_WORKFLOW.md](docs/AGENT_FORMALIZATION_WORKFLOW.md).
That file is intentionally agent-facing and includes the expected prompts,
artifact checklist, validation commands, and workflow rules.

## Development

This project is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

Useful commands:

```bash
lake build EconCSLib.Foundations
python3 scripts/audit_repository.py
```

The full `lake build EconCSLib` target can be temporarily blocked by active
paper work. When that happens, use the narrower build target documented in the
relevant maintenance notes rather than changing unrelated active files.

## More Documentation

- [docs/README.md](docs/README.md): documentation index split into
  human-facing and agent-facing references.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture,
  paper-folder contract, and maintenance notes.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): reusable
  library modules by domain.
- [docs/PROBABILITY_LIBRARY_ROADMAP.md](docs/PROBABILITY_LIBRARY_ROADMAP.md):
  probability-library roadmap.
- [docs/OPTIMIZATION_LIBRARY_ROADMAP.md](docs/OPTIMIZATION_LIBRARY_ROADMAP.md):
  optimization-library roadmap.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md): Lean style conventions.
- [docs/STATUS.md](docs/STATUS.md): controlled vocabulary for paper status.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
