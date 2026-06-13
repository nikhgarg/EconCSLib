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
- Paper assumption file: `TEMPLATE/Assumptions.lean`
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
Keep the dashboard surface small: one row per paper-facing definition or named
result, not every helper theorem, certificate, or proof-route alias.
Every non-derived paper-facing theorem premise must be a named paper assumption
declaration in `Assumptions.lean`, listed in `status.json`
`review_surface.assumption_names`, and checked by `assumption_match_llm.json`
as a true paper/source model assumption.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell. Keep `status.json` as the source of truth for review rows,
artifact paths, and the paper's top-level public status, then run
`python3 scripts/sync_paper_status.py` from the repository root.

At the start of the paper, run the smaller statement target-setting pass before
deep proof work. After the source inventory and first compact
`PaperInterface.lean` skeleton exist, populate `lean_to_tex_llm.json`, populate
`statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper TEMPLATE --statement-precheck`.
Then run `python3 scripts/review_dashboard.py --paper TEMPLATE
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. New
tracked entries should use `{ "tex_statement": "...", "lean_statement_sha256":
"..." }`. Then populate `statement_match_llm.json` with an independent
no-context judgment of whether each translation matches the original paper
statement, including Lean, paper, and TeX statement digests plus the judge
model/agent name, validator type, validation timestamp, and any validator
comment. If the judge flags a mismatch or uncertainty, iterate on the Lean
statement before treating it as the paper theorem target. Run
`python3 scripts/review_dashboard.py --paper TEMPLATE --precheck` before
handoff so missing/stale statement-audit rows are explicit.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare it in `Assumptions.lean`, list it in
`review_surface.assumption_names`, and populate `assumption_match_llm.json`
with an independent source-assumption judgment.
If the dashboard has more than 30 rows, also populate `review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 50 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
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
- [ ] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [ ] Run the assumption/hidden-premise precheck after the statement pass; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 50 or more rows, curate the interface before broad review.
- [ ] Run the context-free Lean-to-TeX translation and third-LLM match judgment
      workflow before asking for human dashboard review.
- [ ] Update `status.json`, then regenerate `papers/status.json`.
- [ ] Update theorem status table after each proof milestone.
- [ ] Rebuild and inspect `DependencyDAG.pdf` after layout edits.

## Post-Formalization Checklist

- [ ] Run a library elevation pass over the paper-local proof modules. Move
      reusable proof results, techniques, certificate constructors, and
      primitives into `EconCSLib` when the destination is clear and the
      extraction is local/low-risk; otherwise record the candidate and likely
      destination module in `FINAL_VALIDATION_REPORT.md`.
