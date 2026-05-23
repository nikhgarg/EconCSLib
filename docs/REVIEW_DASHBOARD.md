# Paper Review Dashboard

The dashboard is the human-facing tool for checking whether each
`PaperInterface.lean` statement matches the corresponding paper statement.
It is for statement validation, not proof search.

`PaperInterface.lean` is the only supported human-review filename. If that file
has grown into a broad helper/proof surface, rename the broad file to an
implementation-facing module such as `ProofInterface.lean`, update imports, and
make `PaperInterface.lean` compact before launching the dashboard.

## Start A Review

Use the paper-local launcher when possible:

```bash
papers/DSWG24DiscretizationBias/review-dashboard.sh
```

Or run the shared script directly:

```bash
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --serve
```

Open one of the printed URLs. On WSL2, the paper-local launcher binds broadly
by default, prints both `127.0.0.1` and any detected WSL guest-IP fallback, and
tries to open those URLs in Windows. Keep the terminal open while it prints
startup status.

## Reviewer Workflow

1. Select the paper.
2. Compare the paper statement, Lean statement, and generated Lean-to-TeX draft.
3. Mark whether the Lean statement matches the paper statement.
4. Add notes for assumptions, source ambiguities, or mismatches.
5. Submit the review row.

The dashboard includes search, status filters, slice filters, source-file
buttons, line numbers, and MathJax rendering for formula-like paper statements.

## Lean-To-TeX Drafts

The Lean-to-TeX draft column can be overridden by a paper-local
`lean_to_tex_llm.json` file in the paper root. Use this for stable,
context-free drafts generated from `PaperInterface.lean` alone, without reading
the source paper. The legacy `.review_traces/lean_to_tex_llm.json` location is
still read when no tracked paper-root draft exists.

## Oversized Interfaces

The dashboard can still filter by `review_slices.json` for legacy oversized
interfaces, but slices are a temporary migration aid, not the desired state.
Before asking a human to review a paper, prefer shrinking `PaperInterface.lean`
to the paper-facing definitions and named results.

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
current Lean statement, paper-facing summary text, and SHA-256 digests. If a
later `PaperInterface.lean` edit changes a reviewed statement, the dashboard
flags that review as stale.

The dashboard's `Reviewed` count means rows in this review log. Treat it as
human review only when the rows were saved by a human reviewer. Agent source
audits should be kept in tracked paper docs such as `SOURCE_AUDIT.md` and
should not be written to `.review_traces/paper_theorem_validations.jsonl` just
to clear the dashboard counter.

Use `--user` to force a reviewer handle. Summary views can be filtered with
`--status-user`.

## Checks And Exports

Run the launch-time freshness check without opening a browser:

```bash
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --precheck
```

Run non-interactive check mode. It exits with code 1 if any selected review is
missing, stale, or marked as not matching:

```bash
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --check
papers/DSWG24DiscretizationBias/review-dashboard.sh --check
```

Export review status:

```bash
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --export-format json
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --export-format csv
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --export-format md
python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --export-format json --status-user nkgarg --stale-only
```

In server mode, machine-readable status is available at:

```text
GET /api/status
GET /api/status?paper=DSWG24DiscretizationBias
GET /api/status?paper=...&slice=slice-01&stale_only=true&user=nkgarg
```

## Launcher Maintenance

New paper scaffolds created with `scripts/new_paper.py` include the paper-local
launcher automatically. For existing paper folders, refresh launchers and cached
paper-interface rows with:

```bash
python3 scripts/bootstrap_review_launchers.py --write --refresh-cache
```
