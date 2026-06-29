# Paper Coverage Audit Workflow

This audit is separate from Lean compilation. A paper can compile while still
having an incomplete or poorly matched human review surface.

## Required Lanes

1. Source inventory.

   Read the source PDF, TeX, or extracted text and build
   `paper_statement_map.json` from the paper itself. Do not build this inventory
   from Lean declaration names. Include theorem/equation numbers, source
   locations, and compact source evidence. Mark final inventories with
   `"source_inventory_kind": "source_curated"` and `"source_curated": true`.

2. Source-to-dashboard matching.

   A separate LLM judge compares each source inventory item with the human
   dashboard rows from `PaperInterface.lean`. Save the result in
   `paper_coverage_llm.json` with:

   - `prompt_version: "paper-coverage-v2-source-grounded-source-to-dashboard"`
   - `audit_kind: "source_to_dashboard_llm"` or `"source_to_dashboard_agent"`
   - `source_grounded: true`
   - `review_rows` naming the Lean dashboard rows for direct or conditional
     dashboard coverage
   - `source_evidence` from the paper
   - a nontrivial reason explaining why the row covers the source item

   Use `conditional_boundary` when the paper statement is represented by a
   dashboard row but the row-local statement judge records an explicit boundary
   assumption. Use `covered_by_support` for named source proof-route lemmas that
   are formalized in support declarations but intentionally not exposed as
   compact dashboard rows; these entries must include `support_declarations`.
   Use `out_of_scope` or `not_a_paper_target` only when the item is intentionally
   not a formalization target.

   Exact key matching from `scripts/seed_paper_coverage.py` is only a scaffold
   and must not be treated as a completed audit.

   This lane fails closed. A missing sidecar, stale prompt version, stale source
   inventory digest, stale dashboard digest, missing validator/model identity,
   missing timestamp, unrecognized verdict, failed judge run, or source item
   without an explicit current success/conditional verdict is an alarm. A blank
   seeded JSON file is pending audit evidence, not passing evidence.

3. Row-local statement translation.

   Generate `lean_to_tex_llm.json` from Lean statements alone. Then compare
   that translation against the source statement in `statement_match_llm.json`.
   This checks whether existing rows say what the paper says; it does not check
   whether all paper statements are present.

4. Joined source-to-Lean validation.

   Run the source-to-dashboard audit against the row-local statement judgments.
   A source item marked `covered` is not clean unless every linked dashboard row
   has a current `statement_match_llm.json` judgment for the same current row
   statement. If a linked row is conditional, the source coverage item must also
   be marked as a conditional boundary.

## Checks

Run:

```bash
python3 scripts/review_dashboard.py --paper <paper-id> --paper-coverage-check
python3 scripts/review_dashboard.py --paper <paper-id> --source-to-lean-check
python3 scripts/review_dashboard.py --paper <paper-id> --statement-check
python3 scripts/review_dashboard.py --paper <paper-id> --assumption-check
```

For public-facing papers, all lanes should be current or the status should
explicitly describe what is missing. If a check cannot run or cannot confirm
success from current inputs, treat the lane as failing until rerun and recorded.
