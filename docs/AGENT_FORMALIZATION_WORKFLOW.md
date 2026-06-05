# Agent Formalization Workflow

This file is for agents and maintainers. The top-level `README.md` is the
human-facing project overview.

## Documentation Split

- Human-facing docs should be strategic, short, and readable without Lean
  expertise. The top-level `README.md`, paper `FINAL_VALIDATION_REPORT.md`
  files, `PaperInterface.lean`, and `DependencyDAG.pdf` are the main human
  surfaces.
- Agent-facing docs may be detailed and operational. This file,
  `docs/ARCHITECTURE.md`, `docs/ECONCSLIB_DOMAIN_INDEX.md`, and
  `skills/econcs-formalizer/` contain workflow rules, implementation
  conventions, and reusable proof guidance.

Do not put long theorem ledgers, raw command transcripts, or proof-internal
details in the top-level README.

## Starting A Paper

Ask the agent to use the `econcs-formalizer` skill and give it the source PDF
or paper URL. A good first prompt is:

```text
Get context on this repo using the skill file. Then start formalizing
<paper title>. Build a source inventory first: every paper definition, named
lemma/proposition/theorem/corollary, and any theorem-like displayed result.
Write and maintain a short proof/formalization plan before proving in Lean.
```

The agent should think through the proof and formalization plan outside Lean
before proving, especially where the paper is underspecified. Keep that plan in
`FORMALIZATION_PLAN.md` and update it as the proof route changes.

## Required Paper Artifacts

Each paper folder should contain:

- `.gitignore`
- `README.md`
- `DependencyDAG.tex`
- `FORMALIZATION_PLAN.md`
- `MainTheorems.lean`
- `PaperInterface.lean`
- `status.json`
- locally cached source PDF, ignored by Git
- locally cached `pdftotext` extraction, when licensing permits

Completed papers should also have:

- `ProofInterface.lean` when implementation-facing theorem endpoints would make
  `PaperInterface.lean` too large to review directly.
- `PostPaperAudit.lean` when an exhaustive source-numbered endpoint ledger is
  useful.
- `FINAL_VALIDATION_REPORT.md` with definitions, named theorem statements,
  proof deviations, assumptions, gaps, and verification outcomes.

## What The Agent Should Keep Current

- `README.md`: source version, status table, and exact caveats.
- `status.json`: paper-local source of truth for paper status, dashboard review
  rows/slices, interface metadata, and artifact paths. After editing it, run
  `python3 scripts/sync_paper_status.py` to regenerate the detailed aggregate
  `papers/status.json`, the compact human-facing `papers/human_status.json`,
  `docs/PAPER_STATUS.md`, the root `README.md` status table, and the
  `site/index.html` status table. Do not hand-edit those generated status files
  or rows.
- `status.json` `human_summary`: public-facing prose for the generated tables.
  If `human_summary_review.status` is `human_approved`, do not rewrite the
  summary unless a human explicitly asks for that exact edit. Audit scripts may
  require a nonempty summary for non-formalized papers, but should not pressure
  edit or shorten human-approved prose.
- `FORMALIZATION_PLAN.md`: lightweight outside-Lean proof scratchpad.
- `DependencyDAG.tex`: proof map with every named result and definition-like
  paper object represented; status and caveat text should agree with
  `status.json`.
- `MainTheorems.lean`: implementation-level source-faithful wrappers.
- `PaperInterface.lean`: the single canonical human-review Lean surface, with
  only readable paper definitions and named theorem statements.
- `ProofInterface.lean`: optional implementation-facing theorem endpoint
  surface for broad wrapper families and proof-seam checks.
- `PostPaperAudit.lean`: exhaustive endpoint ledger when useful.
- `FINAL_VALIDATION_REPORT.md`: final human report.

If the paper proof is imprecise, the agent should build a defensible proof
strategy, formalize that strategy, and record the deviation in the validation
report. It is better to prove a source-faithful theorem by a cleaner route than
to spend large amounts of time following an informal proof line-by-line, as long
as the theorem statement and assumptions are explicit.

## Post-Formalization Closeout

Before declaring a paper complete, run a library elevation pass over the
paper-local proof modules. Check whether any proof results, proof techniques,
certificate constructors, model-neutral definitions, or reusable primitives
should move into `EconCSLib` for other papers to reuse. Elevate local/low-risk
items when the destination module is clear and the build can be checked. If the
move needs broader API design, keep the paper-facing wrapper in place and record
the candidate, destination module, and reusable proof idea in
`FINAL_VALIDATION_REPORT.md`.

## Human Review Order

When the agent says a paper is done, inspect:

1. `FINAL_VALIDATION_REPORT.md`
2. `PaperInterface.lean`
3. `DependencyDAG.pdf`
4. `README.md`
5. `PostPaperAudit.lean`, only if an exhaustive endpoint ledger is needed

The human-facing files should let a reader compare the formalized statements to
the paper without opening lower proof files.

Do not add filename variants for the review surface. If `PaperInterface.lean`
has hundreds of declarations, it is too broad; move helper/proof endpoints into
`ProofInterface.lean` or `PostPaperAudit.lean` and keep the dashboard-facing
file small.

## Validation Commands

For reusable library work, prefer targeted builds first:

```bash
lake build EconCSLib.Foundations
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py
git diff --check
```

For paper work, build the paper root when available:

```bash
lake build papers.<PaperRoot>
```

or the corresponding module target used by the repository.

The full target:

```bash
lake build EconCSLib
```

is the public-release gate and should pass on the public branch. During private
paper development, narrower targets are acceptable for intermediate work, but do
not present a branch as public-ready until the aggregate `EconCSLib` target is
green.

For statement-facing checks, prefer the paper-local launcher from the paper folder:

```bash
./review-dashboard.sh
```

On WSL2, the launcher binds broadly by default and prints multiple Windows
browser URLs when it can detect both localhost and the WSL guest IP. If the
browser does not pop or one URL fails, keep the terminal running and try the
other printed URL. Large interfaces may need several seconds before the first
page responds.

On startup it prints stale-check diagnostics against any existing logged reviews, so
you can refresh only the changed theorem checks and avoid re-validating unchanged items.
The dashboard also shows compact paper-source action links (open PDF/text file) for
quick jumps back to the source statement when needed.
Paper-side formulas are rendered with MathJax when they look like LaTeX.

For a non-interactive pipeline check (exits non-zero when anything is stale or unreviewed):

```bash
./review-dashboard.sh --check
```

If you are working in an older paper folder that already has
`PaperInterface.lean` but no local launcher yet, run once:

```bash
python3 scripts/bootstrap_review_launchers.py --write
```

## Current Maintenance Note

As of 2026-06-01, the public branch passes `lake build EconCSLib`. The auction
theorem aggregate remains a heavy import, so unrelated foundation/probability
work can still use narrower targets during active development, but there is no
current auction theorem-name drift blocking the repository build. If a private
paper thread temporarily breaks an aggregate build, keep that status out of the
public branch or document the exact blocker before review.
