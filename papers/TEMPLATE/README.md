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
- Final validation report: `TEMPLATE/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `TEMPLATE/DependencyDAG.tex`
- Rendered DAG: `TEMPLATE/DependencyDAG.pdf`
- Optional: use `python3 scripts/new_paper.py --with-notes ...` to generate `PAPER_NOTES.md`.

`PaperInterface.lean` should be readable on its own: expose the source formulas
and direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the human-facing surface small: one row per paper-facing definition,
formula, or named source result, not every helper theorem, certificate, or
proof-route alias.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell. Keep `status.json` as the source of truth for review rows,
artifact paths, and the paper's top-level public status, then run
`python3 scripts/sync_paper_status.py` from the repository root.

At the start of a paper, run a statement target-setting pass before deep proof
work. After the source inventory and first compact `PaperInterface.lean`
skeleton exist, use `lean_to_tex_llm.json` for context-free Lean-to-TeX/prose
translations and `statement_match_llm.json` for independent paper-vs-translation
judgments. If a judge flags a mismatch or uncertainty, iterate on the Lean
statement before treating it as the paper theorem target.

At review boundaries, refresh the final validation report's validator ledger
from human review logs and the statement-match sidecars. If the review surface
has more than 30 rows, run a separate row-surface audit and record it in
`review_surface_llm.json`; at 50 or more rows, curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.

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
- [ ] Run the statement target-setting pass and fix mismatched theorem targets
      before serious proof work.
- [ ] Keep `PaperInterface.lean` and `status.json.review_surface` limited to
      source-facing definitions, formulas, and named statements.
- [ ] Update `status.json`, then regenerate `papers/status.json`.
- [ ] Update theorem status table after each proof milestone.
- [ ] Rebuild and inspect `DependencyDAG.pdf` after layout edits.

## Post-Formalization Checklist

- [ ] Run a library elevation pass over the paper-local proof modules. Move
      reusable proof results, techniques, certificate constructors, and
      primitives into `EconCSLib` when the destination is clear and the
      extraction is local/low-risk; otherwise record the candidate and likely
      destination module in `FINAL_VALIDATION_REPORT.md`.
