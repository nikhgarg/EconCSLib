# User Feedback Course Corrections

Last reviewed through: 2026-06-28T18:56:52-04:00

This reference distills recurring user feedback from local Codex history into
candidate workflow rules. It is intentionally separate from the main skill body:
the main skill should stay compact, while this ledger preserves the normalized
corrections that justify future skill updates.

Do not copy these as session history into public docs. When a rule matures,
rewrite it as a direct instruction in the narrowest relevant skill or reference
file. This ledger is provenance, not an operational rulebook for active paper
formalization.

## Extraction Method

Source: `~/.codex/history.jsonl`, filtered for user messages containing
course-correction language such as "do not", "why", "should", "instead",
"too much", "wrong", "mistaken", "remember", "make sure", and repo-specific
terms such as "paper", "formalization", "Lean", "library", "DAG", "audit",
"public/private", "source", "certificate", and "CI".

The pass found 507 course-correction-like messages out of 1307 user history
rows. The clusters below are normalized rules, not quotations.

For future incremental passes, start from rows after the `Last reviewed through`
timestamp above unless the user asks for a full backfill.

## Goal Discipline

Trigger: the user says to keep going on a paper, finish to closure, or work up
to an agreed boundary.

Rule:
- Keep the active paper fixed unless the user explicitly redirects.
- Do not switch to another paper because it seems easier or because nearby
  library work is tempting.
- If another agent owns a paper or proof area, avoid interfering and work only
  on shared library pieces that are clearly safe.
- When the user repeats "keep going", treat it as permission to continue through
  implementation, targeted validation, and the next real proof boundary.

Common failure prevented: drifting into documentation, another paper, or a
smaller local task while the user wanted sustained progress on the active proof.

## Top-Down Proof Planning

Trigger: proof search is becoming local, repetitive, or focused on the smallest
next lemma.

Rule:
- Step back and write a top-down completion plan outside Lean.
- Choose the next action by fastest path to overall paper closure, not easiest
  local proof progress.
- At paper start, identify good partial-formalization boundaries and why they
  are meaningful; surface them to the user before deep proof work.
- If a boundary is accepted, finish everything up to that boundary before doing
  broad docs or unrelated library expansion.

Common failure prevented: spending many turns on tiny lemmas without a credible
route to the paper-facing theorem.

## Source Truth and Source Deviations

Trigger: theorem statements depend on paper conventions, constants, numbering,
or corrected versions.

Rule:
- Download and cache the PDF/TeX/source once; use that local copy for repeated
  checks.
- Prefer the published conference or journal version as source of truth when it
  clarifies assumptions or corrects arXiv text. Link arXiv when useful, but cite
  the published venue for paper metadata where appropriate.
- If a paper has a wrong constant, missing factor, sign issue, or finite-bound
  typo, prove the corrected statement when it is mathematically justified.
- Do not block downstream theorem closure on exact printed algebra if the main
  result only needs a weaker or corrected lemma.
- Document source deviations in the validation/audit report and only surface
  them in tables when they affect a paper-facing result or remaining boundary.

Common failure prevented: repeated web searches, treating source typos as proof
blockers, or burying source deviations in generic prose.

## Caveat, Partial, and Boundary Language

Trigger: a result uses extra assumptions, a source convention is implicit, or a
statement differs from the printed paper.

Rule:
- Use "caveat" for a meaningful source deviation, source error, or missing
  source assumption.
- Use "partial formalization" or "boundary" for proof debt, external library
  debt, or a theorem that still assumes an unproved certificate.
- Do not mark a reasonable source interpretation as a caveat if the result is
  fully proved under that interpretation; explain the interpretation in the
  human-facing report.
- Do not mark definitions as red/caveated merely because they are definitions.

Common failure prevented: making completed results look conditional, or making
conditional results look fully closed.

2026-06-28 update:
- A source-defined convention that intentionally selects, erases, or normalizes
  terms is not a caveat merely because an alternate raw object would differ.
  Keep the paper-facing status focused on whether the source-shaped theorem is
  closed; put convention details in agent-facing audit notes unless they change
  the theorem statement or expose a source-paper issue.
- Human-facing final reports should not carry detailed source-record or
  convention warnings that exist only to prevent future agent confusion.

## Assumption and Certificate Provenance

Trigger: a Lean theorem has model certificates, record fields, row packages, or
opaque wrappers in its assumptions.

Rule:
- "Fully closed" means derived from primitive Lean/mathlib foundations and
  primitive paper assumptions, not merely proved from a certificate.
- Every non-derived certificate field must be recursively traced to either a
  primitive paper assumption, an upstream theorem that derives it, or an
  explicit visible proof boundary.
- Hidden formulas inside records, certificates, library definitions, or source
  rows require provenance checks. Lean can prove wrappers around an incorrect
  formula if the formula is assumed as data.
- Use Lean dependency/axiom-style checks where possible, but supplement them
  with source-provenance audits and LLM review of the eventual assumptions.
- Recursion failure is an audit error, not a silent pass.

Common failure prevented: claiming full formalization when Lean only checked
"hypotheses imply conclusion" and not "hypotheses are source-derived".

## LLM-As-Judge and Audit Hardening

Trigger: statement matching passes but the proof may rely on hidden assumptions
or source-row formulas.

Rule:
- Statement-translation judging is not enough. Add provenance judging for
  assumptions, certificates, and record fields.
- Run a smaller no-context statement/judge pass near the beginning of a paper to
  set correct `PaperInterface.lean` targets.
- Run full post-formalization audit only at closeout or real proof boundaries;
  use targeted checks during active proof work.
- Keep audit code general. Do not add paper-specific function-name heuristics
  where a structural rule can be checked instead.
- Audits of DAGs, validation reports, assumptions, and source records should be
  part of closeout, not optional afterthoughts.

Common failure prevented: LLM judge approving displayed formulas while missing
that they were assumed rather than derived.

2026-06-28 update:
- A compact review surface can be too small as well as too large. Hundreds of
  rows expose implementation internals, but a handful of rows can fail to cover
  the paper claim. For large completed papers, curate a source-level dashboard
  that covers main theorem blocks, key formulas, examples, and appendix pieces.
- `include_names` controls the visible human dashboard, but every other
  `PaperInterface.lean` declaration still needs classification as auxiliary or
  assumption for the closeout audit. Auxiliary slice buckets may satisfy
  readiness checks without expanding the human dashboard.
- After changing source-provenance docstrings, review-surface rows, or
  statement comments, refresh the dashboard cache and regenerate tracked
  sidecars from the current surface; stale sidecars are audit failures even when
  Lean code did not change.

## Library Elevation

Trigger: a proof pattern, definition, or lemma appears useful for multiple
papers or future EconCS papers.

Rule:
- Elevate when at least two papers can use the result, or when future EconCS
  papers in the area are clearly likely to use it.
- Build shared infrastructure for recurring continuous probability, large
  deviations, ranking models, stochastic processes, auctions, matching, social
  choice, algorithms, or optimization patterns.
- Keep paper-facing theorem wrappers, paper-specific certificates, and source
  interpretation text in paper folders.
- After extraction, verify that user-facing theorem statements did not change
  unless a source-deviation update was explicitly approved.

Common failure prevented: either duplicating reusable proofs across papers or
moving paper-specific progress into the public library.

## Documentation Timing

Trigger: proof work is ongoing and docs/status files are being updated often.

Rule:
- Avoid documentation churn while proving. Update README/status/DAG/audit files
  at real session boundaries, proof-boundary changes, public PR preparation, or
  final closeout.
- Do not update `status.json` after every proof loop.
- Do not run full closeout audit when the paper is not done; run targeted checks
  that directly support the active proof.
- Human-facing docs should state current status, not history markers like
  "previously" or "no longer".

Common failure prevented: spending more time synchronizing status artifacts than
closing the proof.

## Human-Facing Documentation Standards

Trigger: updating README, DAG, validation reports, public tables, website, or
paper dashboards.

Rule:
- Human summaries should be concise, current, and paper-facing.
- Avoid dumping long Lean declaration lists. Usually record one main Lean
  declaration per paper-facing result.
- Paper-specific status tables may include rare source-deviation notes, but
  public summary tables should stay sparse.
- DAG nodes for completed results should summarize mathematical content, not
  say only "closed" or "formalized".
- Review dashboards should expose paper-named results and displayed formulas,
  not every helper lemma.
- Keep DAG arrowheads, caveat coloring, and dependency density aligned with the
  workflow template.

Common failure prevented: public/human docs becoming internal debugging logs.

## Public and Private Repository Hygiene

Trigger: committing, pushing, merging, opening public PRs, or syncing private
and public repositories.

Rule:
- Private main is acceptable for routine private work unless the user asks for a
  branch.
- Do not rebase private repos frequently; do it only for substantial changes or
  when needed for sync.
- Public PRs must be filtered: do not expose unpublished partial papers,
  private source caches, text caches, or private-only artifacts.
- Before merging public work, confirm CI/audit expectations, website/table
  regeneration, line counts, and status files are correct.
- If private and public diverge, preserve private proof progress and publish
  only the intended public subset.

Common failure prevented: accidentally publishing partial private formalizations
or losing private proof work during library extraction.

## Runtime and Tooling

Trigger: shell commands fail with stream-fd errors, repeated source lookups, or
slow status synchronization.

Rule:
- On this Ubuntu setup, use `login=false` for shell commands to avoid repeated
  `Failed to create stream fd: Operation not permitted` failures.
- Cache downloaded paper sources and use local copies.
- Do not keep searching the web after source is available locally.
- Do not wait on private CI unless the task requires merging, diagnosing CI, or
  the user explicitly asks.

Common failure prevented: losing proof time to repeated environment and source
lookup overhead.

## Subagents and Concurrent Work

Trigger: using subagents or working while another agent is active.

Rule:
- Use subagents for independent source checks, proof-route comparison, library
  search, and audit validation.
- Give subagents narrow tasks and ask for artifacts or conclusions, not broad
  open-ended proof ownership.
- Do not work on a paper another agent is actively formalizing unless the user
  tells you to. Shared library changes are acceptable when coordinated and
  minimally disruptive.

Common failure prevented: duplicated or conflicting work across active agents.

## Promotion Checklist

Before moving any rule from this ledger into `skills/econcs-formalizer`:

1. Remove references to the session that taught the lesson.
2. Remove paper-specific notation unless the destination is a paper-specific
   reference.
3. Phrase the lesson as an action or check, not a retrospective explanation.
4. Put math-specific content in a math/proof reference file, not the main skill.
5. Keep public-release rules separate from proof-search rules when possible.
