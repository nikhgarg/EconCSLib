# [Paper Title]

## Source Version
- Paper: *[Title]*
- Authors: [Authors]
- Version formalized: [Conference/Journal/ArXiv version]
- Official URL: [URL]
- Public PDF: [URL]

The PDF is not committed to git (ignored via `.gitignore`), but a local copy should be kept in this directory for reference.
The extracted source text cache should be kept beside it locally when useful,
but should remain ignored by Git in public workspaces unless redistribution
rights have been checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `TEMPLATE/MainTheorems.lean`
- Human-facing theorem file: `TEMPLATE/PaperInterface.lean`
- Machine-readable status source: `TEMPLATE/status.json`
- Outside-Lean proof plan: `TEMPLATE/FORMALIZATION_PLAN.md`
- Dependency DAG: `TEMPLATE/DependencyDAG.tex`
- Rendered DAG: `TEMPLATE/DependencyDAG.pdf`
- Optional: use `python3 scripts/new_paper.py --with-notes ...` to generate `PAPER_NOTES.md`.

`PaperInterface.lean` should be readable on its own: expose the source formulas
and direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell. Keep `status.json` as the source of truth for review rows,
artifact paths, and the paper's top-level public status, then run
`python3 scripts/sync_paper_status.py` from the repository root.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Main theorem(s) | `none` | not started | `none` | Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`, then add matching rows |

## Intake Checklist

- [ ] Fill in all metadata fields in this template.
- [ ] Copy the paper theorem/lemma list from the local source text cache before drafting the DAG.
- [ ] Fill in `FORMALIZATION_PLAN.md` with the initial proof strategy and
      likely hard seams before deep Lean work.
- [ ] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`.
- [ ] Update `status.json`, then regenerate `papers/status.json`.
- [ ] Update theorem status table after each proof milestone.
- [ ] Rebuild and inspect `DependencyDAG.pdf` after layout edits.
