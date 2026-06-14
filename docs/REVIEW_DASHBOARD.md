# Paper Review Dashboard

The dashboard is the human-facing tool for checking whether each
`PaperInterface.lean` statement matches the corresponding paper statement.
It is for statement validation, not proof search.

`PaperInterface.lean` is the only supported human-review filename. If that file
has grown into a broad helper/proof surface, rename the broad file to an
implementation-facing module such as `ProofInterface.lean`, update imports, and
make `PaperInterface.lean` compact before launching the dashboard.
It should expose only paper-facing definitions, formulas, and named statements.
If the dashboard row count is much larger than the paper's named definitions and
results, curate `review_surface.include_names` in `status.json` and move helper
or certificate endpoints out of `PaperInterface.lean` before asking for review.
The dashboard enforces two row-count prompts: more than 30 rows requires a
current `review_surface_llm.json` audit that checks whether all rows are
paper-facing, and 50 or more rows shows an oversized-surface warning even when
an audit exists.

## Start A Review

Use the paper-local launcher when possible:

```bash
papers/ABC24ShortTitle/review-dashboard.sh
```

Or run the shared script directly:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --serve
```

Open one of the printed URLs. On WSL2, the paper-local launcher binds broadly
by default, prints both `127.0.0.1` and any detected WSL guest-IP fallback, and
tries to open those URLs in Windows. Keep the terminal open while it prints
startup status.

## Reviewer Workflow

1. Select the paper.
2. Compare the paper statement, Lean statement, and generated Lean-to-TeX draft.
3. Check the independent statement-match judgment when one is available.
4. Mark whether the Lean statement matches the paper statement.
5. Add notes for assumptions, source ambiguities, or mismatches.
6. Submit the review row.

The dashboard includes search, status filters, slice filters, source-file
buttons, line numbers, and MathJax rendering for formula-like paper statements.
It reads the paper-local `status.json` `review_surface` section as the
machine-readable source of truth for curated review rows and slices.

## Lean-To-TeX Drafts

The Lean-to-TeX draft column can be overridden by a paper-local
`lean_to_tex_llm.json` file in the paper root. Use this for stable,
context-free drafts generated from `PaperInterface.lean` alone, without reading
the source paper. The legacy `.review_traces/lean_to_tex_llm.json` location is
still read when no tracked paper-root draft exists.

The intended workflow has three independent statement passes:

1. The formalization agent writes the compact paper-facing Lean statement in
   `PaperInterface.lean`.
2. A second LLM, given only that Lean statement and no paper context, translates
   it to paper-style LaTeX/prose and saves the result in `lean_to_tex_llm.json`.
3. A third LLM, given only the original paper statement and the translated
   LaTeX/prose, judges whether they match and saves the result in
   `statement_match_llm.json`.
4. A separate assumption-provenance LLM, given only the paper source text for
   the claimed assumptions and the assumption declarations from `Assumptions.lean`,
   judges whether every listed assumption is truly a paper/source model
   assumption rather than a proof shortcut. Save this in
   `assumption_match_llm.json`.

The statement match pass is full-theorem and formula-level, not just
result-label-level. Every displayed equation, inequality, iff, definition, or
source-defining formula that is part of a paper-facing result should have an
exact review row or an exact subclaim row. Broad rows that merely say a numbered
result's metrics, model, or source surface are formalized can hide sign errors,
missing normalizers, domain restrictions, omitted subparts, or premise
shortcuts. The Lean-to-TeX prompt should preserve every visible binder,
hypothesis, domain condition, equivalence/implication direction, and conclusion.
The judge prompt should explicitly ask whether all formula-bearing subclaims are
present and whether their hypotheses, subparts, quantifiers, signs, constants,
normalizations, inequality direction, domains, and conclusions match the
complete original paper statement. Conditional wrappers, source-row/certificate
packages, omitted conclusions, or weakened/strengthened statements must be
judged `mismatch` or `uncertain`.

Formula rows are still subject to proof provenance. A source-equation wrapper
is complete only when it is derived in Lean from the paper's source model
primitives or from separately validated paper assumptions. If the formula is
asserted as a source row, theorem premise, certificate field, capacity identity,
normalization, or other undischarged proof boundary, record it in
`Assumptions.lean`/`assumption_match_llm.json` or mark the downstream endpoint
partial until it is derived.

The same rule applies to reusable library certificates. A library theorem may
require an explicit certificate or source-shaped package from its caller; that
is a good reusable API. But a paper-facing theorem is not complete merely
because it aliases that library theorem. The paper wrapper must construct the
certificate from paper primitives, or the certificate must be a validated paper
assumption. Otherwise the dashboard/report should show a partial or conditional
boundary. Use `python3 scripts/audit_repository.py --library-only --library-premise-audit` to
list reusable APIs with certificate/source-boundary parameters and to catch
paper rows that transitively depend on those APIs through helper layers.
The default repository audit also follows paper-local helper chains. A reviewed
row is blocked if any local helper it depends on, recursively, still consumes an
unvalidated certificate, source-row equation, hidden hypothesis, or
proof-boundary premise. Internally constructed certificates are fine; hidden
premise consumers are not. Axioms, constants, opaque declarations, and unsafe
declarations are review blockers.

If the third LLM reports a mismatch or uncertainty, edit the Lean statement, not
the translation, unless the translation is plainly wrong. The statement being
iterated is the theorem that should be formalized. Re-run the Lean-to-TeX and
judge passes after changing `PaperInterface.lean`.

Use this workflow in two modes:

- Initial target-setting pass: run near the beginning of a paper, after the
  source inventory and first `PaperInterface.lean` skeleton, before investing in
  long proofs. This lightweight pass only establishes that the Lean statements
  are the right formalization targets. Generate `lean_to_tex_llm.json` from the
  full expanded Lean statements, generate `statement_match_llm.json` against the
  complete original paper theorem/definition/formula text, run
  `python3 scripts/review_dashboard.py --paper <paper> --statement-precheck`,
  then run `python3 scripts/review_dashboard.py --paper <paper>
  --assumption-precheck`. The statement judge is row-local; it does not certify
  that visible theorem premises are source assumptions or already-derived facts.
  Iterate on `PaperInterface.lean` until mismatches and premise-provenance
  findings are fixed. Do not update the final validation report,
  review-surface audit, DAG, or human-review log just for this early pass.
- Full review-boundary pass: run before handoff, before public release, and
  after major `PaperInterface.lean` statement changes. This includes the same
  Lean-to-TeX and statement-judge pass, plus the review-surface audit when row
  count requires it, the assumption-provenance pass when assumptions exist, the
  `Statement Translation Audit` section in
  `FINAL_VALIDATION_REPORT.md`, and the full `--precheck`.

For both modes, every dashboard row needs one concrete source statement. If the
automatic TeX/text extraction is missing, over-broad, or pulls in surrounding
paragraphs, repair the source-facing statement text before asking the judge to
compare. Otherwise the judge may correctly return `uncertain` even when the Lean
target is mathematically right.

Declaration-keyed source statements belong in a source-inventory/report section,
not in generated audit output. The dashboard ignores `Statement Translation
Audit` when extracting source statements; that section is downstream evidence,
not source text for the next judge pass.

If all or nearly all rows are `uncertain`, treat that as a likely source
statement extraction or parser issue. Fix the source map, or record one
paper-wide source-map problem, before accepting a long row-by-row uncertain
list.

`lean_to_tex_llm.json` has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "prompt_version": "lean-to-tex-v2-strict-context-free",
  "translator": "gpt-5-codex",
  "translator_type": "model",
  "translated_at": "2026-06-13T12:00:00Z",
  "prompt_summary": [
    "Translate from the Lean statement alone, with no paper context.",
    "Preserve all visible binders, hypotheses, domains, directions, and conclusions."
  ],
  "items": {
    "paper_theorem_name": {
      "tex_statement": "Context-free paper-style translation of the Lean statement.",
      "lean_statement_sha256": "optional digest"
    }
  }
}
```

For older papers, item values may also be plain strings containing the
translation; the dashboard accepts both forms.

`statement_match_llm.json` is optional and tracked in the paper root when used.
It has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "prompt_version": "statement-match-v2-strict-full-statement",
  "validator": "gpt-5-codex",
  "validator_type": "model",
  "validated_at": "2026-06-06T12:00:00Z",
  "prompt_summary": [
    "Compare the complete source statement against the Lean-to-TeX translation.",
    "Require exact agreement on hypotheses, subparts, quantifiers, domains, constants, normalizations, signs, inequality directions, and conclusions."
  ],
  "comment": "Optional sidecar-wide validator note.",
  "items": {
    "paper_theorem_name": {
      "matches": true,
      "judgment": "matches",
      "reason": "The translated statement has the same hypotheses and conclusion.",
      "comment": "Optional validator-facing note.",
      "lean_statement_sha256": "optional digest",
      "paper_statement_sha256": "optional digest",
      "tex_statement_sha256": "optional digest"
    }
  }
}
```

Use `matches: false` or `"judgment": "mismatch"` for a failed check, and
`"judgment": "uncertain"` when the judge cannot decide. If the optional digests
are present and the current Lean, paper, or TeX statement changes, the dashboard
marks the saved LLM judgment as stale. These LLM checks do not count as human
dashboard reviews.

Top-level `validator`, `validator_type`, `validated_at`, and `comment` fields
are defaults; an item entry may override them when a different model or agent
checked that specific row.

Status exports include a machine-readable `validators` ledger for each row.
Human dashboard reviews enter this ledger with `validator_type: "human"` and
the saved GitHub/user handle. Statement-match sidecars enter the same ledger
with the recorded model or agent name, timestamp, judgment, and comment. The
compact `validator_names` column is for tables; the detailed `validators` array
is the source of truth for dates, comments, sources, and stale flags.

`--precheck` reports statement-translation audit warnings separately from human
review rows. It flags missing Lean-to-TeX drafts, stale Lean-to-TeX drafts,
missing statement-judge entries, stale judge entries, mismatches, uncertain
judgments, and unknown judgment values. JSON exports include these paper-level
summaries under `statement_audits`.

`--statement-precheck` reports only the statement-translation audit lane, which
is useful for the initial target-setting pass. `--statement-check` is the same
check with a non-zero exit when any statement-audit row is missing, stale,
uncertain, mismatched, or otherwise invalid.

The repository audit enforces this for completed papers as well. A paper marked
`formalized` or `formalized with caveat` should not pass
`python3 scripts/audit_repository.py` if its statement-translation sidecars or
review-surface sidecar are stale, missing, uncertain, mismatched, or otherwise
flagged. Treat the dashboard check as the fast paper-local diagnostic and the
repository audit/CI as the backstop.

## Assumption Provenance

Paper-facing theorem hypotheses are allowed only when they are explicit source
assumptions. Do not hide a capacity equation, threshold identity, density row,
certificate, or proof convenience as an unreviewed theorem premise. Instead:

1. Add a named assumption declaration in paper-local `Assumptions.lean`,
   usually named `assumption_*`, `paper_assumption_*`, or
   `source_assumption_*`.
2. Use that named assumption in theorem signatures, for example
   `(h_model : assumption_source_model_conditions params)`.
   The theorem statement may reference the imported assumption; the assumption
   declaration itself should not live in `PaperInterface.lean` unless this is
   legacy code awaiting cleanup.
3. List every assumption declaration in paper-local `status.json`
   `review_surface.assumption_names`.
4. Save an independent source-assumption judgment in
   `assumption_match_llm.json`.

For new proof work, prefer deriving the premise or using the named assumption
declaration directly in the theorem signature. For existing broad
paper-local audit ledgers, the repository audit also accepts exact
`-- audit-premise: <binder name> : <binder type>` markers attached to an
approved `Assumptions.lean` declaration. This is a migration aid for making
hidden source-model premises visible across `ProofInterface.lean` and
`PostPaperAudit.lean`; it should not become a way to accumulate proof-only
certificates.

`assumption_match_llm.json` has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "prompt_version": "assumption-provenance-v2-exact-premise-source",
  "validator": "gpt-5-codex",
  "validator_type": "model",
  "validated_at": "2026-06-06T12:00:00Z",
  "prompt_summary": [
    "Validate each assumption declaration and every exact audit-premise.",
    "A premise is acceptable only when it is source text, a source model primitive, a theorem condition, or derived in Lean from source primitives."
  ],
  "comment": "Optional sidecar-wide validator note.",
  "items": {
    "assumption_source_model_conditions": {
      "judgment": "paper_condition",
      "reason": "The condition is stated in the model section or theorem statement.",
      "source_location": "Section 2, paragraph 3",
      "premise_judgments": {
        "hDomain : 0 < parameter": {
          "judgment": "source_text_model_primitive",
          "source_location": "Section 2, model paragraph",
          "reason": "The source model states the positive-parameter domain."
        },
        "hBridge : derived_formula = source_formula": {
          "judgment": "partial_boundary",
          "source_location": "Appendix proof, equation display",
          "reason": "The source uses this formula, but Lean has not yet derived it from the primitive model."
        }
      },
      "comment": "Optional validator-facing note.",
      "lean_statement_sha256": "optional digest",
      "paper_statement_sha256": "optional digest"
    }
  }
}
```

Use `"judgment": "paper_assumption"` for a standalone paper/model assumption,
`"paper_condition"` for a theorem-domain condition stated in the source model
or theorem statement, `"documented_caveat"` for a known source mismatch or
intentional source-statement repair, and `"partial_boundary"` for an
undischarged external/library/analytic/runtime/solver boundary that keeps the
paper partial. Use `"judgment": "not_paper_assumption"` when the row is a proof
assumption, certificate boundary, or derived formula that is not explicitly
assumed by the paper. Use `"judgment": "uncertain"` when the judge cannot
decide from the source text. The dashboard flags missing, stale, uncertain,
unknown, partial-boundary, and not-paper-assumption declarations under the
paper-level assumption panel.

Grouped assumption judgments are not enough. If `Assumptions.lean` contains
`-- audit-premise:` comments, every exact premise must appear under
`premise_judgments`. Use `source_text_model_primitive`, `source_text`, or
`paper_condition` only when the premise is explicitly a source/model/theorem
condition and cite the source location. Use `derived_from_source_primitives`
only when the Lean development already derives the premise from prior source
definitions. Use `partial_boundary` when the premise is visible but not yet
source-matched or derived; a paper with any `partial_boundary` premise must be
reported as partial, not fully formalized.

The assumption judge must not accept a formula merely because it appears in a
source proof or because a Lean helper can consume it. Displayed equations,
capacity identities, threshold cutoffs, normalizations, density or mass rows,
source-row packages, certificates, and witness objects are source assumptions
only if the source states them as assumptions or theorem hypotheses. Otherwise
they must either be derived in Lean from source primitives or recorded as a
partial boundary.

Run `python3 scripts/audit_repository.py` at the same boundary. The repository
audit does not stop at the compact `PaperInterface.lean` declaration text: it
follows thin `abbrev`/`def` aliases into paper-local Lean files and scans
paper-facing declarations such as `paper_interface_*` across the paper folder.
Thus a certificate, threshold equation, capacity identity, source-row package,
or proof-boundary premise hidden in `ProofInterface.lean` is still a review
blocker unless it is derived or appears as a validated paper-assumption
declaration.

`--assumption-precheck` reports only this lane and also invokes the repository
hidden-premise audit for the selected paper. `--assumption-check` is the same
check with a non-zero exit when any assumption declaration is missing, stale,
uncertain, judged not to be a paper assumption, or any paper-facing theorem
premise is still not routed through `Assumptions.lean`. Full `--precheck`
includes this lane.

Because the hidden-premise lane expands Lean declarations, assumption checks may
need built `.olean` artifacts even when a paper has no explicit
`Assumptions.lean` rows. If a fresh checkout is slow locally, use the JSON
dashboard export only for triage and rely on the full repository audit in CI
before declaring the paper clean.

## Review-Surface Audit

For any paper whose dashboard has more than 30 rows, run a separate LLM pass
before broad human review. Give that LLM the dashboard row names and paper-facing
summaries, but no proof context, and ask whether every row is a paper-facing
definition, formula, or named source statement that belongs in the human review
surface. Save the result in paper-root `review_surface_llm.json`.

At 50 or more rows, the dashboard always shows an oversized-surface warning.
That warning is intentional: even if the LLM audit passes, a human should first
decide whether the paper truly has that many named paper-facing rows or whether
implementation helpers leaked into `PaperInterface.lean`.

`review_surface_llm.json` has schema:

```json
{
  "schema": 1,
  "paper": "PaperFolder",
  "validator": "gpt-5-codex",
  "validator_type": "model",
  "validated_at": "2026-06-06T12:00:00Z",
  "comment": "Optional sidecar-wide validator note.",
  "judgment": "passes",
  "reason": "The rows are exactly the paper-facing definitions and numbered results.",
  "review_rows": 42,
  "review_surface_sha256": "digest printed by the dashboard export/API",
  "items": {
    "paper_theorem_name": {
      "judgment": "keep",
      "reason": "Named source theorem."
    }
  }
}
```

Use `"judgment": "needs_curation"` when helper, diagnostic, certificate, or
proof-route rows should be removed from the human review surface. Use
`"judgment": "uncertain"` when the LLM cannot tell. If `review_rows` or
`review_surface_sha256` no longer matches the current dashboard rows, the
dashboard marks the audit stale. This audit does not increment human review
counts.

## Interface Size

Before asking a human to review a paper, shrink `PaperInterface.lean` to the
paper-facing definitions and named results. Put broad proof aliases in
`ProofInterface.lean` or another implementation-facing module, then expose the
curated source-facing review rows in paper-local `status.json`.

```bash
wc -l papers/<Paper>/PaperInterface.lean
rg -c '^(noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev) ' papers/<Paper>/PaperInterface.lean
```

## Review Logs

By default, reviews are written under each paper folder:

```text
papers/<PaperName>/.review_traces/paper_theorem_validations.jsonl
```

Each row stores the reviewer handle, UTC timestamp, match decision, notes,
current Lean statement, paper-facing summary text, source-provenance metadata,
and SHA-256 digests. If a later `PaperInterface.lean` edit changes a reviewed
statement or a nontrivial source-deviation note, the dashboard flags that
review as stale.

When a `PaperInterface.lean` docstring is a literal source statement, mark it
with a dashboard-only line such as `Source status: direct paper statement` or
`Source status: direct paper formula`. When the displayed statement is edited
from the source, corrected, weakened, strengthened, or added as an audit row,
add `Source status: ...` and `Source note: ...` lines explaining the deviation.
The dashboard strips these lines out of the paper-statement text and surfaces
them separately as source-provenance badges.
For formula-bearing rows, the source-provenance note must identify whether the
formula is a direct paper formula, a corrected source formula, a derived formula
from source primitives, or an explicit paper assumption. Do not use a generic
numbered-result summary as the source statement for multiple displayed
formulas.

The repository is configured so that `paper_theorem_validations.jsonl` is
commit-eligible, while other `.review_traces` files such as local dashboard
logs, rendered statement caches, generated HTML, and parser caches remain
ignored. After a human review pass, inspect and commit the paper-local
`paper_theorem_validations.jsonl` file if those judgments should become part of
the repository history.

The dashboard's `Reviewed` count means rows in this review log. Treat it as
human review only when the rows were saved by a human reviewer. Agent source
audits should be kept in tracked paper docs such as `SOURCE_AUDIT.md` and
should not be written to `.review_traces/paper_theorem_validations.jsonl` just
to clear the dashboard counter.

The reviewer field is editable in the browser. By default it is prefilled from
`--user`, then GitHub identity (`GITHUB_ACTOR`-style environment variables or
the username authenticated in `gh`), then git config, then the OS username.
Use `--user` to force a reviewer handle. Summary views can be filtered with
`--status-user`.

## Checks And Exports

Run the launch-time freshness check without opening a browser:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --precheck
```

Run non-interactive check mode. It exits with code 1 if any selected review is
missing, stale, or marked as not matching:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --check
papers/ABC24ShortTitle/review-dashboard.sh --check
```

Export review status:

```bash
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format json
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format csv
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format md
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format validators-md
python3 scripts/review_dashboard.py --paper ABC24ShortTitle --export-format json --status-user <github-user> --stale-only
```

Use `validators-md` to refresh the paper-facing validator table in
`FINAL_VALIDATION_REPORT.md`. It lists every dashboard/PaperInterface row, the
validators recorded for that row, and validator comments.

In server mode, machine-readable status is available at:

```text
GET /api/status
GET /api/status?paper=ABC24ShortTitle
GET /api/status?paper=...&slice=slice-01&stale_only=true&user=<github-user>
```

## Launcher Maintenance

New paper scaffolds created with `scripts/new_paper.py` include the paper-local
launcher automatically. For existing paper folders, refresh launchers and cached
paper-interface rows with:

```bash
python3 scripts/bootstrap_review_launchers.py --write --refresh-cache
```
