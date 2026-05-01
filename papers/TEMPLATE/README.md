# [Paper Title]

## Source Version
- Paper: *[Title]*
- Authors: [Authors]
- Version formalized: [Conference/Journal/ArXiv version]
- Official URL: [URL]
- Public PDF: [URL]

The PDF is not committed to git (ignored via `.gitignore`), but a local copy should be kept in this directory for reference.
The extracted source text cache should be kept beside it when licensing permits.

## Paper-Facing Ledger

- Human-facing theorem file: `TEMPLATE/MainTheorems.lean`
- Dependency DAG: `TEMPLATE/DependencyDAG.tex`
- Rendered DAG: `TEMPLATE/DependencyDAG.pdf` when generated locally

`MainTheorems.lean` should expose the source formulas and paper-facing theorem
wrappers directly. Do not mark a row `formalized` unless the Lean declaration is
closed and the remaining assumptions cell is `None`.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Theorem 1 | `paper_theorem_1` | formalized | `TEMPLATE/MainTheorems.lean` | None |
