# Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States

## Source Version

- Paper: *Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States*
- Authors: Nikhil Garg; Wes Gurnee; David Rothschild; David Shmoys
- Version formalized: arXiv:2107.07083; Operations Research 2026, DOI 10.1287/opre.2024.1167
- Official URL: https://pubsonline.informs.org/doi/abs/10.1287/opre.2024.1167
- Public PDF: https://arxiv.org/pdf/2107.07083.pdf

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt` when `pdftotext` succeeds, and is also ignored by Git in
public workspaces unless redistribution rights have been checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `GGRS26CombattingGerrymanderingRCV/MainTheorems.lean`
- Human-facing theorem file: `GGRS26CombattingGerrymanderingRCV/PaperInterface.lean`
- Machine-readable status source: `GGRS26CombattingGerrymanderingRCV/status.json`
- Outside-Lean proof plan: `GGRS26CombattingGerrymanderingRCV/FORMALIZATION_PLAN.md`
- Final validation report: `GGRS26CombattingGerrymanderingRCV/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `GGRS26CombattingGerrymanderingRCV/DependencyDAG.tex`
- Rendered DAG: `GGRS26CombattingGerrymanderingRCV/DependencyDAG.pdf`

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the dashboard surface small: one row per paper-facing definition or named
result, not every helper theorem, certificate, or proof-route alias.

Use the controlled status vocabulary from `../../docs/STATUS.md`. Public-facing
rows should use `partially formalized` for results that still depend on an
external theorem, certificate, or proof boundary, and should name that boundary
in the final column rather than using `conditional` as a separate status label.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, fill in the `FORMALIZATION_PLAN.md`
`Initial Outside-Lean Paper Audit` section before deep proof work. Read the
source, sanity-check every named result and formula-bearing displayed claim for
signs, constants, normalizations, quantifiers, domains, and dependencies, and
record suspected bugs, missing assumptions, formula ambiguities, and proof
strategy consequences. The initial plan is a hard start gate: include the
source/version inventory, complete named-result ledger, formula/dependency
sanity pass, shared-library reuse checkpoint, and formal target/boundary map
before serious theorem proving. Alert the user early about any major issue.
After that source inventory and the first compact `PaperInterface.lean`
skeleton exist, run the smaller statement target-setting pass: populate
`lean_to_tex_llm.json`, populate `statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --statement-precheck`.
Also populate `paper_statement_map.json` for the paper's source definitions,
formulas, and named claims, then run the paper-level coverage pass and save
`paper_coverage_llm.json`: this asks whether every source statement that should
be represented is covered by at least one dashboard row. This source-to-row
accounting is separate from the row-local statement judge.
Then run `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. The
translator must preserve every visible variable, binder, hypothesis, domain
condition, equivalence direction, and conclusion; it must not summarize a theorem
as an endpoint label or omit conditions that appear in the Lean statement. New
tracked entries should use `{ "tex_statement": "...", "lean_statement_sha256":
"..." }`. Then populate `statement_match_llm.json` with an independent
no-context judgment of whether each translation matches the original full paper
statement, including all hypotheses, subparts, quantifiers, domains, constants,
normalizations, signs, inequality directions, and conclusions. A row may be
judged `matches` only if it is equivalent to the full source statement or to a
clearly identified source subpart; if the Lean translation is a conditional
wrapper, source-row package, omitted subclaim, weakened/strengthened statement,
or broad aggregate for several displayed formulas, the judge must mark
`mismatch` or `uncertain`. Include Lean, paper, and TeX statement digests plus
the judge model/agent name, validator type, validation timestamp, and any
validator comment. If the judge flags a mismatch or uncertainty, iterate on the
Lean statement before treating it as the paper theorem target. Run
`python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --precheck` before
handoff so missing/stale statement-audit rows are explicit.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare that hypothesis in `Assumptions.lean`, list it in
`status.json` `review_surface.assumption_names`, and populate
`assumption_match_llm.json` with an independent judgment that it is a true
paper/source model assumption rather than a proof shortcut.
The repository audit follows paper-local helper chains recursively: a theorem
is not closed if any helper it depends on still consumes an unvalidated
certificate, source-row equation, hidden hypothesis, or proof-boundary premise.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to bypass that
provenance boundary.
If the dashboard has more than 30 rows, also populate `review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 120 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.
Before a full-formalization closeout, rerun
`python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --paper-coverage-precheck`
and resolve missing, stale, partial, or uncertain source coverage.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Thiele/PAV committee-score vocabulary | `PartyApprovalBallot`, `partyPAVScore`, `paper_pav_score` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Real-valued PAV wrapper over `EconCSLib.SocialChoice.Voting.Thiele` |
| PAV seat-score and min-argmax definitions | `pavSeatScore`, `pavSeatMinArgmax`, `paper_pav_seat_score`, `paper_pav_min_argmax` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source formula for the two-party PAV objective and leftmost argmax selector |
| Lemma C.1 interval characterization | `pavSeatInterval`, `paper_pav_seat_interval` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source-shaped interval `y_R (M + 1) - 1 <= n_R < y_R (M + 1)` |
| Lemma C.1 PAV argmax-to-interval statement | `pavSeatMinArgmax_seatInterval`, `paper_pav_min_argmax_seat_interval` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Closed via reusable harmonic marginal-weight lemmas in `EconCSLib.SocialChoice.Voting.Thiele` |
| Lemma C.1 interval-to-rounding bridge | `pavSeatInterval_seatShareRounded`, `paper_pav_interval_seat_share_rounded` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Closed reusable arithmetic bridge via `EconCSLib.SocialChoice.Voting.pavSeatInterval_roundedSeatShare` |
| Proposition 1 rounding target | `seatShareRounded`, `paper_seat_share_rounded` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source-shaped target for `{floor (y_R M), ceil (y_R M)}` |
| Proposition 1 STV solid-coalition terminal process | `paper_stv_solid_coalition_process_bounds` | formalized | `PaperInterface.lean` | Source-facing predicate for the appendix same-party quota-process outcome; no paper-local assumption declaration remains |
| Proposition 1 STV quota-capacity step | `paper_stv_quota_floors_fit` | formalized | `PaperInterface.lean` | Closed reusable Droop-quota arithmetic: the two parties' full quota floors fit within `M` seats |
| Proposition 1 STV process-to-quota-witness bridge | `paper_stv_solid_coalition_process_bounds_quota_witness_bounds`, `paper_stv_solid_coalition_quota_witness_bounds` | formalized | `PaperInterface.lean` | Closed bridge from terminal same-party process certificates to quota witnesses via `Voting.STV.SolidCoalition`; direct quota lower bounds are equivalent to this boundary in `MainTheorems.lean` |
| Proposition 1 STV quota-witness-to-lower-bound bridge | `paper_stv_solid_coalition_quota_witness_bounds_lower_bounds`, `paper_stv_solid_coalition_lower_bounds` | formalized | `PaperInterface.lean` | Closed quota-witness arithmetic via `Voting.STV.Quota` |
| Proposition 1 STV lower-bound-to-rounding bridge | `paper_stv_solid_coalition_lower_bounds_seat_share_bounds`, `paper_stv_seat_share_bounds` | formalized | `PaperInterface.lean` | Closed reusable two-party proportionality bridge via `Voting.Proportionality` |
| Proposition 1: STV/PAV rounded seat shares | `paper_proposition1_from_stv_bounds_and_pav_min_argmax` | formalized | `PaperInterface.lean` | Lean-closed theorem from the formal solid-coalition STV outcome predicate and the formalized PAV min-argmax theorem |
| Redistricting optimization and simulations | `none` | not formalized | `none` | Data/code boundary outside the 19-row theorem ledger |

## Intake Checklist

- [ ] Confirm the official PDF URL, version, and bibliographic fields.
- [ ] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [ ] Fill in `FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [ ] Record the shared-library reuse checkpoint: mathlib, cslib, optlib, and
      `EconCSLib` modules/declarations inspected; API chosen; near-misses.
- [ ] Record the formal target map: rows to prove, empirical/out-of-scope rows,
      and any explicit boundary that would remain if the paper cannot close now.
- [ ] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [ ] Run the assumption/hidden-premise precheck after the statement pass; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Confirm `python3 scripts/audit_repository.py` reports no recursive
      paper-local hidden-premise dependency or axiom-like declaration for this
      paper.
- [ ] Populate `DependencyDAG.tex` with the same named-result inventory.
- [x] Replace initial placeholders in `MainTheorems.lean` and
      `PaperInterface.lean` before updating any status row.
- [ ] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 120 or more rows, curate the interface before broad review.
- [ ] Run the context-free Lean-to-TeX translation and third-LLM match judgment
      workflow before asking for human dashboard review.
- [ ] Update `status.json`, then run `python3 scripts/sync_paper_status.py`.
- [ ] Rebuild `DependencyDAG.pdf` and verify visually after each significant edit.

## Post-Formalization Checklist

- [x] Run a library elevation pass over paper-local proof modules and record
      reusable candidates or completed extractions in `FINAL_VALIDATION_REPORT.md`.
- [x] Update `DependencyDAG.tex`, rerender `DependencyDAG.pdf`, inspect the
      rendered diagram, and record the DAG audit evidence in both
      `FINAL_VALIDATION_REPORT.md` and `POST_FORMALIZATION_AUDIT.md`.
- [x] Run the targeted repository audit after the report/DAG updates:
      `python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0`.
      This audit includes the DAG/final-report closeout gate; resolve all
      findings for this paper before claiming the post-formalization workflow is
      complete.
- [ ] Run the combined recursive provenance audit and write a closeout report:
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`.
      Resolve all findings for this paper before claiming `formalized`; if a
      finding remains, mark the result partial/conditional in `status.json`,
      `DependencyDAG.tex`, and `FINAL_VALIDATION_REPORT.md`.
