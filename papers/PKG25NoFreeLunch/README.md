# A No Free Lunch Theorem for Human-AI Collaboration

## Source Version

- Paper: *A No Free Lunch Theorem for Human-AI Collaboration*
- Authors: Kenny Peng, Nikhil Garg, Jon Kleinberg
- Version formalized: Proceedings of the AAAI Conference on Artificial Intelligence, 39(13), 14369–14376 (AAAI 2025)
- Official URL: https://ojs.aaai.org/index.php/AAAI/article/view/33574
- Public PDF: https://ojs.aaai.org/index.php/AAAI/article/download/33574/35729
  (ArXiv: https://arxiv.org/pdf/2411.15230.pdf)

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt` when `pdftotext` succeeds, and is also ignored by Git in
public workspaces unless redistribution rights have been checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `PKG25NoFreeLunch/MainTheorems.lean`
- Human-facing theorem file: `PKG25NoFreeLunch/PaperInterface.lean`
- Machine-readable status source: `PKG25NoFreeLunch/status.json`
- Outside-Lean proof plan: `PKG25NoFreeLunch/FORMALIZATION_PLAN.md`
- Final validation report: `PKG25NoFreeLunch/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `PKG25NoFreeLunch/DependencyDAG.tex`
- Rendered DAG: `PKG25NoFreeLunch/DependencyDAG.pdf`

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the dashboard surface small: one row per paper-facing definition or named
result, not every helper theorem, certificate, or proof-route alias.

Use the controlled status vocabulary from `../../docs/STATUS.md`:
`formalized`, `formalized with caveat`, `partially formalized`, `conditional`,
`scaffold`, `not started`, and `not formalized`. Keep detailed caveats,
remaining certificates, or proof-route notes in the final column rather than in
the status cell.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, run the smaller statement target-setting pass before
deep proof work. After the source inventory and first compact
`PaperInterface.lean` skeleton exist, populate `lean_to_tex_llm.json`, populate
`statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper PKG25NoFreeLunch --statement-precheck`.
Use this pass only to correct theorem targets; do not update the DAG, final
validation report, human-review log, or review-surface audit just because this
early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. New
tracked entries should use `{ "tex_statement": "...", "lean_statement_sha256":
"..." }`. Then populate `statement_match_llm.json` with an independent
no-context judgment of whether each translation matches the original paper
statement, including Lean, paper, and TeX statement digests plus the judge
model/agent name, validator type, validation timestamp, and any validator
comment. If the judge flags a mismatch or uncertainty, iterate on the Lean
statement before treating it as the paper theorem target. Run
`python3 scripts/review_dashboard.py --paper PKG25NoFreeLunch --precheck` before
handoff so missing/stale statement-audit rows are explicit.
If the dashboard has more than 30 rows, also populate `review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 50 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Rounding convention | `definition_rounding_convention` | formalized | `PaperInterface.lean` | `round(1/2) = 1` |
| Collaboration strategy | `definition_collaboration_strategy` | formalized | `PaperInterface.lean` | Deterministic strategy, matching the source theorem |
| Interior prediction profiles | `definition_interior_prediction_profile` | formalized | `PaperInterface.lean` | Source constrains `(0,1)^n` |
| Non-collaboration | `definition_non_collaborative` | formalized | `PaperInterface.lean` | Fixed agent away from ties and fixed tie label |
| Reliability | `definition_reliable` | formalized | `PaperInterface.lean` | Source reliability over all collaboration settings |
| Main theorem | `theorem_main_no_free_lunch` | formalized | `PaperInterface.lean` | Source-implicit nonempty agent set; proof restricts reliability to finite witness settings |

## Intake Checklist

- [x] Confirm the official PDF URL, version, and bibliographic fields.
- [x] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [x] Fill in `FORMALIZATION_PLAN.md` with the initial proof strategy and
      likely hard seams before deep Lean work.
- [x] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [x] Populate `DependencyDAG.tex` with the same named-result inventory.
- [x] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
      before updating any status row.
- [x] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [x] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 50 or more rows, curate the interface before broad review.
- [x] Run the context-free Lean-to-TeX translation and third-LLM match judgment
      workflow before asking for human dashboard review.
- [x] Update `status.json`, then run `python3 scripts/sync_paper_status.py`.
- [x] Rebuild `DependencyDAG.pdf` and verify visually after each significant edit.
