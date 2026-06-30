# Capacity Constraints Make Admissions Processes Less Predictable

## Source Version

- Paper: *Capacity Constraints Make Admissions Processes Less Predictable*
- Authors: Evan Dong; Nikhil Garg; Sarah Dean
- Version formalized: AAAI-26 published version, cross-checked against
  arXiv:2601.11513v1 TeX source
- Official URL: https://ojs.aaai.org/index.php/AAAI/article/view/41179
- DOI: https://doi.org/10.1609/aaai.v40i45.41179
- Open TeX/PDF source: https://arxiv.org/abs/2601.11513
- Public PDF cache source: https://arxiv.org/pdf/2601.11513.pdf

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt` when `pdftotext` succeeds, and is also ignored by Git in
public workspaces unless redistribution rights have been checked separately.
The arXiv TeX source is cached under `source_tex/` and is the working source of
truth for formulas and theorem labels. The AAAI page is the canonical
publication/documentation link.

## Paper-Facing Ledger

- Implementation theorem file: `DGD26AdmissionsPredictability/MainTheorems.lean`
- Human-facing theorem file: `DGD26AdmissionsPredictability/PaperInterface.lean`
- Machine-readable status source: `DGD26AdmissionsPredictability/status.json`
- Outside-Lean proof plan: `DGD26AdmissionsPredictability/FORMALIZATION_PLAN.md`
- Final validation report: `DGD26AdmissionsPredictability/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `DGD26AdmissionsPredictability/DependencyDAG.tex`
- Rendered DAG: `DGD26AdmissionsPredictability/DependencyDAG.pdf`
- Clean LAP variability proof note:
  `DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.tex`
- Rendered LAP variability proof note:
  `DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.pdf`

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the dashboard surface curated but complete: one row per paper-facing
definition, formula, example, remark, proposition, theorem/corollary, and
main-text lemma that a reviewer or LLM-as-judge should inspect. Do not omit
source-visible named material merely to keep the dashboard compact. Appendix
theorems/corollaries should be represented; appendix lemmas are a judgment call,
but if they carry paper-facing mathematical content needed for the formalized
claim, expose review-legible rows rather than hiding them in a broad support
bundle.

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
`python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --statement-precheck`.
Also populate `paper_statement_map.json` for the paper's source definitions,
formulas, and named claims, then run the paper-level coverage pass and save
`paper_coverage_llm.json`: this asks whether every source statement that should
be represented is covered by at least one dashboard row. This source-to-row
accounting is separate from the row-local statement judge. A source-visible
definition, example, remark, proposition, theorem/corollary, or main-text lemma
must not be marked `out_of_scope`/`not_a_paper_target` just because the review
surface would grow; add a row and let the row-local statement judge inspect it.
Then run `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. The
translator must preserve every visible variable, binder, hypothesis, domain
condition, named predicate/wrapper application, equivalence direction, and
conclusion; it must not summarize a theorem as an endpoint label, source-like
phrase, or proof route, or omit conditions that appear in the Lean statement.
New tracked entries should use `{ "tex_statement": "...",
"lean_statement_sha256": "..." }`. Then populate `statement_match_llm.json`
with an independent no-context judgment of whether each translation matches the
original full paper statement, including all hypotheses, subparts, quantifiers,
domains, constants, normalizations, signs, inequality directions, conclusions,
and visible inputs. A row may be judged `matches` only if it is semantically
equivalent to the full source statement or to a clearly identified source
subpart, and every input premise is accounted for as a paper primitive/source
assumption, a Lean-derived consequence of those primitives, or an explicit
conditional boundary. The judge must inspect named Lean predicates/wrappers
semantically, not approve by theorem label, phrase overlap, or source-looking
name. If the Lean translation is a conditional wrapper, source-row package,
certificate/replay/process/bridge package, omitted subclaim,
weakened/strengthened statement, hidden strengthening inside a named predicate,
or broad aggregate for several displayed formulas, the judge must mark
`mismatch` or `uncertain`. Include Lean, paper, and TeX statement digests plus
the judge model/agent name, validator type, validation timestamp, and any
validator comment. If the judge flags a mismatch
or uncertainty, iterate on the Lean statement before treating it as the paper
theorem target. Run
`python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --precheck` before
handoff so missing/stale statement-audit rows are explicit.
All audit sidecars are fail-closed. Blank scaffolded files, missing prompt
versions, stale prompt versions, missing current digests, missing
validator/model identity, missing timestamps, unrecognized judgments, failed
judge runs, and items without explicit success verdicts remain audit alarms
until rerun against the current Lean/source inputs.
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
For public-facing closeout, populate a current `review_surface_llm.json` even
when the dashboard has 30 or fewer rows; the row threshold is an early review
prompt, not a final-audit exemption.
Before a full-formalization closeout, rerun
`python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --paper-coverage-precheck`
and resolve missing, stale, partial, or uncertain source coverage.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Base finite choice-function theory | `paper_zero_distance_statement`, `paper_substitutability_one_instability_equivalence_statement`, `paper_even_instability_inconsistency_forward_statement`, `paper_even_instability_inconsistency_converse_statement` | formalized | `PaperInterface.lean` | None; zero-instability, independence, consistency, substitutability iff 1-instability, instability calculation, the even-instability iff directions, and the `2q` instability ceiling are proved. The no-zero-instability statement exposes the standard nontrivial capacity condition. |
| q-representative queues | `paper_q_representative_characterization_statement`, `paper_q_representative_converse_statement`, `paper_q_representative_variability_at_most_one_statement`, `paper_q_representative_general_variability_at_most_one_statement`, `paper_acceptant_one_instability_variability_general_variability_at_most_one_statement`, `paper_q_representative_general_variability_exactly_one_statement`, `paper_acceptant_one_instability_variability_general_variability_exactly_one_statement`, `paper_q_representative_variability_exactly_one_statement`, `paper_q_representative_borderline_eq_waitlisted_after_changing_insert_statement`, `paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement` | formalized | `PaperInterface.lean` | None; under feasibility, q-representativeness is equivalent to q-acceptance, 1-instability, and variability at most one. Exact-one rows expose the corresponding nondegenerate displacement witness. |
| Sequential-queue variability | `paper_sequential_composition_q_acceptant_statement`, `paper_sequential_additive_variability_bound_statement`, `paper_sequential_q_representative_choice_properties_statement`, `paper_sequential_q_representative_variability_bound_statement` | formalized | `PaperInterface.lean` | None; feasibility, summed-capacity q-acceptance, preservation of substitutability, additive variability, and the q-representative queue variability bound are proved. |
| Append/remove variability bridge | `paper_waitlisted_witness_exact_exchange_statement`, `paper_waitlisted_family_subset_borderline_after_matched_removals_statement`, `paper_waitlisted_set_card_le_some_borderline_set_card_statement`, `paper_append_remove_variability_at_most_equivalence_statement`, `paper_append_remove_variability_exact_equivalence_statement`, `paper_borderline_witness_exact_exchange_statement` | formalized | `PaperInterface.lean` | None; exact one-for-one exchange lemmas and the all-`m` threshold/exact equivalence between appendix general variability and main-text borderline variability are proved for feasible q-acceptant 1-unstable rules. |
| LAP ordering lemma | `paper_lap_ordering_statement`, `paper_lap_strictly_higher_slot_applicant_assigned_statement`, `paper_lap_no_rejected_slot_below_statement`, `paper_lap_no_profitable_one_slot_swap_of_objective_optimal_statement` | formalized | `PaperInterface.lean` | None; proved from a primitive finite assignment/no-profitable-one-slot-swap model, with global objective optimality plus capacity filling implying the local no-profitable-swap condition. |
| LAP assignment-choice bridge | `paper_lap_assignment_selector_feasible_choice_statement`, `paper_lap_assignment_selector_q_acceptant_statement`, `paper_lap_assignment_one_instability_statement`, `paper_lap_assignment_variability_at_most_slots_statement`, `paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement` | formalized | `PaperInterface.lean` | None; feasible capacity-filling unique global-optimum assignment selectors induce feasible q-acceptant 1-unstable choice rules, and the distinct-ordering variability theorem is proved by a directed alternating-splice/proper-suffix exchange. |
| Tight instability constructions | `paper_calculating_instability_statement`, `paper_q_acceptant_two_q_instability_bound_statement`, `paper_tight_max_even_instability_family_statement`, `paper_tight_max_odd_instability_family_statement`, `paper_padded_even_tight_instability_family_statement`, `paper_padded_odd_tight_instability_family_statement`, `paper_tight_one_instability_example_statement`, `paper_tight_two_instability_example_statement`, `paper_tight_three_instability_example_statement`, `paper_tight_four_instability_example_statement`, `paper_tight_five_instability_example_statement` | formalized | `PaperInterface.lean` | None; padded even and odd trigger-switch constructions prove feasible q-acceptant tight `d`-instability for every `1 ≤ d ≤ 2q`. |
| Empirical NYC program instantiations and performance study | `none` | not formalized | `none` | Private-data empirical plots, model-performance measurements, and concrete program-class queue decompositions are descriptive/source-instantiation material outside the Lean theorem target. |

## Intake Checklist

- [x] Confirm the official PDF URL, version, and bibliographic fields.
- [x] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [x] Fill in `FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [x] Record the shared-library reuse checkpoint: mathlib, cslib, optlib, and
      `EconCSLib` modules/declarations inspected; API chosen; near-misses.
- [x] Record the formal target map: rows to prove, empirical/out-of-scope rows,
      and any explicit boundary that would remain if the paper cannot close now.
- [x] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [x] Run the assumption/hidden-premise precheck after the statement pass; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [x] Run the source-record/boundary-input audit if any reviewed theorem uses a
      record, certificate, replay, process, bridge, source-row, or broad package
      premise.
- [x] Confirm `python3 scripts/audit_repository.py` reports no recursive
      paper-local hidden-premise dependency or axiom-like declaration for this
      paper.
- [x] Populate `DependencyDAG.tex` with the same named-result inventory.
- [x] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
      before updating any status row.
- [x] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [x] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [x] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 120 or more rows, curate the interface before broad review.
- [x] Run the context-free Lean-to-TeX translation and independent semantic match judgment
      workflow before asking for human dashboard review.
- [x] Update `status.json`.
- [x] Rebuild `DependencyDAG.pdf` and verify visually after each significant edit.

## Post-Formalization Checklist

- [x] Run a library elevation pass over paper-local proof modules and record
      reusable candidates or completed extractions in `FINAL_VALIDATION_REPORT.md`.
- [x] Update `DependencyDAG.tex`, rerender `DependencyDAG.pdf`, inspect the
      rendered diagram, and record the DAG audit evidence in both
      `FINAL_VALIDATION_REPORT.md` and `POST_FORMALIZATION_AUDIT.md`.
- [x] Run the targeted repository audit after the report/DAG updates:
      `python3 scripts/audit_repository.py --paper DGD26AdmissionsPredictability --paper-closeout --include-active --info-limit 0`.
      This audit includes the DAG/final-report closeout gate; resolve all
      findings for this paper before claiming the post-formalization workflow is
      complete.
- [x] Run the targeted recursive provenance/source-record closeout audit and
      record the result in `POST_FORMALIZATION_AUDIT.md`. Resolve all findings
      for this paper before claiming `formalized`; if a finding remains, mark
      the result partial/conditional in `status.json`, `DependencyDAG.tex`, and
      `FINAL_VALIDATION_REPORT.md`.
