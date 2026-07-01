---
name: econcs-formalizer
description: Formalize economics-and-computation papers in Lean. Use when asked to add, continue, triage, or plan Lean formalizations of EC/ACM EC/SIGecom-style papers; formalize finite, continuous, probabilistic, or measure-theoretic theorem seams; extract reusable primitives; repair Lean/mathlib proof scripts; or prepare general handoff guidance for future formalization work.
---

# EconCS Formalizer

Use this skill to turn economics-and-computation papers into maintainable Lean
code. Keep repository-specific status out of this file; in `EconCSLib`, that
belongs in `docs/ECONCSLEAN_CURRENT_STATUS.md`.

For new Lean files, new shared-library APIs, new paper-facing declarations, and
code already being substantially rewritten, follow
`skills/lean-community-conventions/SKILL.md`. Apply those conventions
forward-looking only: do not start broad repository-wide renaming, formatting,
import, or documentation refactors during active proof work unless the user
explicitly asks for a cleanup pass. Paper-local source-indexed names may remain
when needed for source auditability; shared reusable APIs should follow the
convention style.

When updating skills from prior sessions or user corrections, use
`skills/econcs-session-insights/SKILL.md` as the provenance workflow. Promote
durable day-to-day formalization rules into this skill or its proof references;
do not leave them as a parallel operational rulebook in the session-insights
skill.

When planning automation-heavy formalization workflows, multi-agent proof
campaigns, retrieval-grounded statement translation, or compiler-guided repair
loops, also consult `skills/ai-formalization-workflows/SKILL.md`. That skill is
a source-credited ledger of external AI-formalization workflow patterns; this
formalizer skill remains the operational rulebook for EconCSLib.

When syncing `EconCSLib-private` and `EconCSLib-public`, preparing public PRs
from private work, copying generated DAG/report PDFs, or reconciling audit
sidecars across sibling checkouts, read
`skills/econcs-formalizer/references/public-private-sync.md` first. Use that
semantic sync workflow instead of raw repository merges or broad folder copies.

## Component 1: Workflow and Organization

### 1.1 Core Rule

Formalize theorem seams, not PDFs. Start from the paper's precise definitions,
the main result to be checked, and the smallest reusable lemmas needed to close
that result.

When a paper source has already been downloaded into the repository, treat that
local TeX/text cache as the working source of truth. Do not keep repeating web
searches for the same source during proof work. If the source is missing and
the exact TeX/later-version convention is needed, first check sibling public,
private, recovered, and archived worktrees for an existing cache and copy it
into the active paper folder. Only download when no local cache exists. Record
where the local cache lives, then use that copy for subsequent source checks.
Prefer source TeX over PDF text extraction for displayed formulas, numbered
equations, theorem labels, and appendix proof steps; PDF text is often good
enough for orientation but too noisy to settle algebraic disputes.

Use `formalized` as the repository status word for Lean-checked paper results.
Lean verification is the mechanism, not a separate paper status. Do not answer
status questions with "verified in Lean" when the intended claim is
`formalized`; reserve "reviewed" for saved human dashboard review entries and
"validation" for the audit/checking workflow.
Treat `status.json` human-facing notes as human-authored copy, even when a
field is marked `draft`. Do not add, elaborate, summarize, or reframe
`human_summary`, public notes, website notes, or paper-table comments unless
the user explicitly asks for that exact prose change. If the user asks to
remove a phrase, remove only that phrase and preserve the remaining text. If
the user says a note should be empty, set the source field to the empty string
and regenerate script-owned surfaces from that source. Put technical audit
details in validation reports, handoffs, or machine-readable audit sidecars,
not in sparse public/paper notes.
Treat `formalized` as a strong provenance claim: every exposed paper result is
proved by Lean from imported Lean/mathlib/library declarations plus explicit
theorem parameters that are either discharged by the proof or recorded as
validated paper-source assumptions. The LLM-as-judge checks are necessary audit
evidence that the exposed Lean statements and explicit assumptions match the
source paper, but they are not themselves Lean proofs and they do not certify
hidden premises. Before saying a whole paper is fully formalized, confirm the
Lean-native axiom audit (`#print axioms` via `scripts/audit_repository.py`),
the row-local statement checks, and the visible-premise/source-assumption
checks are current and clean for that paper. Treat any user request for a
"Lean axiom" or "axiom dependency" check on a paper result as a request for
the recursive repository audit path, not a single ad hoc `#print axioms` call:
the audit must expand the paper-facing row, follow paper-local aliases and
relevant library declarations, then call Lean's axiom printer on the resulting
declarations and report hidden premises/certificate APIs along the path.
When the user explicitly approves closing a paper modulo one external theorem,
prefer a single theorem-shaped, paper-local axiom over a broad endpoint axiom.
The axiom should state the external library theorem or theorem bundle being
imported, such as a stochastic-convergence or fixed-dimension solver theorem,
while deterministic paper source semantics are still encoded as concrete source
model records and bridge theorems. The final audit must expose exactly the
named axiom, plus approved Lean foundations, and the paper status/report must
call the result conditional or axiom-boundary until that theorem is proved in
the library.
Treat source-formula correctness as a separate provenance obligation from
statement text matching. Lean can prove an internally consistent theorem whose
inputs already contain a wrong displayed formula; an LLM statement judge can
also miss that the formula was assumed rather than derived. For every
formula-bearing paper result, know where the formula enters the proof:
definition body, derived lemma, explicit validated source assumption, or
partial boundary. A result is not fully formalized merely because the final
wrapper has the right-looking theorem text.
Run a recursive abstraction-debt audit whenever a paper-facing row depends on a
record, certificate, replay, process, semantics object, source model, bridge,
package, or consequences bundle. Expand the theorem's visible premises and then
inspect every input semantically against the paper source model; names are only
routing hints and are never evidence by themselves. For each input, either
identify the exact paper primitive/source assumption it corresponds to, cite the
Lean-checked constructor theorem that derives it from those primitives, route it
through an approved external boundary, or mark the row conditional/partial.
For `Certificate`, `Replay`, `Process`, and `Bridge` inputs in particular, the
audit must ask for an instantiation path from the paper's primitive model, not
just a source-looking type name or theorem wrapper.
Then inspect the fields of every such structure recursively until each field is
classified as a proved Lean consequence, an imported shared-library theorem, a
validated paper-source formula/assumption, a recursively audited container
field, a derived consequence-record output, a non-propositional witness datum,
an approved external proof boundary, or unresolved proof debt. The
LLM-as-judge prompt for these rows must explicitly ask whether any theorem
input or field smuggles in the result being claimed, a displayed formula,
trajectory generation, convexity, continuity, equilibrium, response semantics,
replay/trace validity, transfer preservation, or convergence that should have
been derived. Rows whose proof merely projects an opaque field such as `trace`,
`replay`, `process`, `bridge`, `directionalField_eq`,
`convex_solutionSpace`, `response`, `isMax`, `convergence`, or `continuity` are
conditional on instantiating that field, even if Lean compiles and the
top-level theorem statement matches the paper. Mark those rows as source-model
boundaries or proof debt unless a separate reviewed row proves the field from
more primitive paper assumptions.
The recursive audit is a search for an eventual source-backed leaf, not a
permission to stop at an intermediate Lean package. If a paper-facing theorem
assumes a field that is not directly a source definition/model primitive, the
audit must point to the upstream theorem or nested field that derives it from
source primitives. If that chain cannot be followed because a structure is
missing, the maximum depth is reached, a cycle appears, or a nested container is
classified as an ordinary source assumption, treat it as an audit error: a Lean
statement is not backed by the source until the derivation chain reaches a
validated source assumption, a proved primitive consequence, or an explicitly
approved external boundary.
This recursive audit must be code-backed before closeout. Run or extend the
skill helper
`python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper <paper-folder> --out papers/<paper-folder>/audit/source_record_audit.json`
so the audit payload is generated from the current Lean files, includes Lean
`#check` output for the paper rows and structure fields, and gives the LLM judge
the actual kernel-checked statements rather than a prose summary. The judge
must classify every source-record field as `proved_from_primitives`,
`validated_source_assumption`, `approved_external_boundary`,
`nonpropositional_witness_data`, or `unresolved_assumed_math`; it may use
`container_recursively_audited` only for a
field whose type is another audited source/record/certificate and whose nested
fields are separately judged, and `derived_consequence_record` only for theorem
output records whose constructor proof is checked and whose premise records are
separately audited. Use `nonpropositional_witness_data` only for bare data
witnesses whose type is not proposition-valued and does not itself state a
formula, equality, recurrence, optimality, measurability, convergence,
continuity, response semantics, or trajectory semantics; the proof fields that
constrain those witnesses must still be audited separately. Do not accept
`matches` for a row whose decisive math appears only as a record field
projection.
At a real closeout/publication boundary, the provenance gate invokes
`python3 scripts/audit_repository.py --paper <paper-folder> --paper-closeout --include-active --info-limit 0`.
During active formalization on an unfinished paper, do not run that closeout
gate unless the user explicitly asks for post-validation; use targeted Lean
builds, placeholder scans, and row-scoped LLM-as-judge checks for the exact
changed statements, assumptions, or source-record fields. Do not start the full
dashboard/sidecar/final-report audit loop merely because a proof-surface row,
source record, or status entry changed while the paper is still known
unfinished. If a proof pass adds or changes source-record fields, run the
code-backed recursive audit or LLM judge only for those changed records/rows
when needed to prevent hidden assumptions, but defer full dashboard prechecks,
full statement sidecar regeneration, DAG/final-report audit updates, and
`--paper-closeout` until the paper is actually done or the user explicitly asks
for that validation phase. The eventual closeout gate must report missing,
stale, or unresolved `source_record_audit.json` /
`source_record_match_llm.json` sidecars as assumption/provenance findings.
Treat `PaperInterface.lean` as a closed review surface, not a scratch file.
Every declaration exported there must be classified in `status.json`
`review_surface.include_names`, `review_surface.assumption_names`, or
`review_surface.auxiliary_names`. Use `auxiliary_names` only for proof-facing
helpers intentionally excluded from statement review, and never to hide a named
paper theorem or a non-source premise. If a helper theorem needs a
`...Certificate`, `...Model`, `...Semantics`, `...Bridge`, `...Package`,
`...Inputs`, `...Process`, or `...Consequences` premise that is not itself
derived from prior Lean code, keep it in
`ProofInterface.lean`/`MainTheorems.lean` unless it is a reviewed row or a
validated assumption/proof boundary. During active proof work, after a
`PaperInterface.lean` edit run targeted checks for the changed declarations and
premises; do not enter the full dashboard/sidecar workflow solely because the
review surface changed. At closeout or user-requested post-validation, run
`python3 scripts/review_dashboard.py --paper <paper-folder> --precheck` or the
paper-specific machine-status audit; a clean statement-judge sidecar alone is
not evidence that hidden premises or unreviewed helpers are absent.
Before creating a paper-local definition, record, theorem family, or reusable
`EconCSLib/` primitive for a common proof seam, do a dependency and
shared-library context load. Search imported upstream libraries first:
`Mathlib/` for mathematical structures and theorems, `Cslib/` for computer
science and runtime notions, and `Optlib/` when it exists in the workspace or
Lake manifest for optimization-specific APIs. Prefer those definitions and
results over creating local replacements. If an upstream API almost fits, add a
thin bridge lemma or source-facing notation around it; only introduce a new
library primitive after recording why the upstream API is not adequate.
Search `EconCSLib/` next for the domain noun and proof shape:
equilibrium/best-response/a.e.
exception, threshold/cutoff, CDF/quantile/PIT/tie-breaking, finite mixture,
Gaussian/admissions/testing, LP/certificate, ranking/social choice, auction, or
large-deviation. Open the most relevant shared files and reference notes before
adding local scaffolding. If a reusable API exists, import and specialize it.
This check belongs in the initial outside-of-Lean plan for every paper and
again whenever a proof loop starts building wrappers around a standard concept.
Also search related paper folders, especially completed or recently active
papers in the same domain, before adding paper-local machinery. Many reusable
algorithmic layers first appear inside a paper folder before being promoted to
`EconCSLib/`; do not reinvent a simulator, runner, trace generator, dynamic
process, checker pattern, certificate, or source-model constructor until you
have searched sibling papers for the same domain nouns and declaration shapes.
If two papers need the same machinery, elevate the common core into the shared
library or route the current paper through the existing reusable paper layer as
an interim step, rather than creating parallel incompatible APIs. Record in the
outside-of-Lean plan which related paper folders were checked and why the chosen
API is the one to build on. If the user, notes, or repository history suggest a
specific same-domain paper already built the machinery, pause implementation and
inspect that paper plus its imports before adding new declarations.
For continuous equilibrium work in particular, check
`EconCSLib.Foundations.Optimization.ChoiceEquilibriumAE`,
`StrategicEquilibrium`, and the admissions/testing probability modules before
defining a local equilibrium or distributional interface.
For continuous optimization or geometry work, assume mathlib probably already
has the basic objects: norms and distances on finite products, `WithLp`/`PiLp`,
inner-product and finite-dimensional spaces, Frechet/scalar derivatives,
convexity/concavity/extrema, projections, Holder inequalities, and special
function derivative rules. Search and reuse these before writing formula-level
norm, derivative, convexity, projection, or argmax APIs in `EconCSLib/`.
The outside-of-Lean plan must contain a short "shared-library reuse checkpoint"
before any substantial proof campaign: list the shared declarations or modules
inspected, including relevant mathlib/cslib/optlib candidates, the API chosen,
and any near-miss that was intentionally not used. If that checkpoint is
missing, add it before continuing. If a proof loop starts
creating several local wrappers around a standard notion, pause and update this
checkpoint instead of continuing the wrapper stack. A reusable concept should
enter the paper proof through the shared API unless the plan explains the
source-specific obstruction.
In particular, do not use a syntactic recursive dependency scan as the primary
proof-debt test. Lean already knows the transitive proof dependencies of a
closed theorem: `#print axioms` must report only approved standard foundations
such as `propext`, `Classical.choice`, and `Quot.sound`. Use the expanded
`#check`/dashboard premise audit for visible theorem hypotheses, and use
source-shaped library/API hygiene to prevent paper formulas from being hidden
inside reusable definitions. The formula audit must be recursive: if a
paper-facing theorem uses a library definition or theorem whose parameters,
fields, or body encode a source displayed formula, the LLM-as-judge workflow
must inspect the expanded formula or a proved paper-local equivalence to it.
This audit must include paper-local structures as well as reusable library
definitions. For every source-semantics record, add a brief field provenance
table in the paper plan, handoff, validator ledger, or status notes before
calling the row fully formalized. If the desired theorem should follow from
paper assumptions but currently follows only because a record field states the
needed fact, the correct next step is to refine the source model or prove a
constructor from primitive assumptions, not to let the record field pass through
the assumption judge as ordinary source text.
The source-record audit is not satisfied by a natural-language list of fields.
It must be generated from code that parses the review rows, recursively follows
record/certificate/source-model types, and feeds those row and field types back
through Lean. If the helper misses a local pattern, patch the helper or the
repository audit before accepting the LLM result. The LLM judge should see the
source text, Lean `#check` output, dependency path, and field provenance, and it
must answer the narrower question: is this mathematical source statement proved
by earlier Lean declarations, or is it merely assumed by a source field?
Do not allow "the library definition says it" to substitute for source-formula
validation. Ordinary source-visible theorem conditions such as positivity,
measurability, or ordering hypotheses should be validated by the
statement/assumption judges, but they are not the same thing as global proof
debt.
If a paper theorem cannot be derived without an extra geometric/model premise,
do not force that premise through the source-assumption judge just to keep the
headline theorem. Expose the exact missing formula as a record-free predicate,
prove the strongest no-hidden-premise alternative (for example `conclusion ∨
¬ missing_formula`), and separately prove any exact restricted theorem whose
extra condition really discharges the formula. The paper report and statement
judge should mark the restricted theorem as a conditional boundary rather than
a match to the unrestricted source theorem.
The hardened repository audit is standard-based, not function-name-based. It
rebuilds declaration indexes each run, follows paper-local aliases for visible
premises, asks Lean for transitive axioms, scans reusable library declarations
for certificate/source-boundary APIs, rejects reusable `Assumption` or
`Hypothesis` declarations, rejects paper/source provenance wording in
`EconCSLib/*.lean`, and checks generic code/docs for concrete paper IDs,
citation prefixes, or paper theorem-number labels. Put paper metadata in
paper-local files or data config; keep `EconCSLib/`, audit scripts, and generic
workflow docs paper-neutral. If a citation-like term is truly an established
algorithm/domain name, record that as a data-configured allowlist entry rather
than a code exception. This audit reduces hidden-premise and generic-code
drift, but it still does not prove source formulas correct by itself; do the
outside-Lean formula sanity pass and derive formula-bearing claims from
primitives whenever possible.
Shared-library comments and docstrings are part of this generic surface: do
not describe reusable results as "Theorem 1", "Lemma 2", or by a paper ID even
when the result was extracted for a paper. Use paper-neutral mathematical
language such as "finite-product likelihood factorization" and leave the
paper-number crosswalk in the paper folder, final report, or status metadata.

Unless told otherwise, you do not have a time limit; keep going until you reach
the requested stopping condition or a clean theorem/compile boundary. Run the
full post-paper checklist, review-dashboard/audit workflow, and polished
`FINAL_VALIDATION_REPORT.md` update only when the paper is genuinely finished
or the user explicitly asks for post-validation. For intermediate progress on
an unfinished paper, use targeted Lean builds and a short status/handoff update
instead of spending tokens on the full audit/report cycle. Do not run
`scripts/audit_repository.py --paper <paper> --paper-closeout` for routine
progress on a paper that is still `partially formalized`, `conditional`, or
known to have remaining library/proof-boundary work, unless the user explicitly
requests closeout/post-validation or the next action is a public PR/release
handoff. In-progress checks should normally be limited to the edited Lean
targets, JSON/line-count sanity checks, placeholder scans, and optional
row-scoped LLM-as-judge checks for newly changed statements, assumptions, or
source-record fields. Defer dashboard prechecks and full sidecar/report
regeneration until the paper is actually done or the user requests
post-validation.

Do not confuse "keep going" with broad exploration or with optimizing for the
fastest next small lemma. Default to a top-down completion plan for the whole
paper. Start from the named paper results that remain unclosed, identify the
source-model or library layer that would discharge each visible certificate or
conditional premise, and order the work by the shortest route to full
paper-level closure. Use small theorem batches as the execution unit only
after that overall route is clear, and choose those batches because they remove
a paper-facing obstacle on the completion path. Avoid adding local helper
wrappers merely because they are easy unless they visibly reduce the final
theorem assumptions or turn a documented source-model gap into a proved bridge.

Once the top-down route is clear, move in tight compile/proof loops: identify
the current paper-facing theorem seam, make a coherent batch of edits, run only
the requested or necessary targeted build, and patch the compiler's concrete
line errors. Avoid rereading large files after you already know the relevant
structure; use `rg` for exact declaration names and narrow line windows around
compiler diagnostics.
If an active proof batch edits shared `EconCSLib/` library code, still stay in
the targeted-build loop: build the touched library module or namespace root and
the active paper root that imports it. Do not run a broad/full repository build
merely because a shared library file changed while the paper is still in
progress. Save broad builds for natural stopping points: the paper is complete
or being handed off, you are about to commit/push a significant integration
batch, preparing a public PR/release, or the user explicitly asks for a broad
integration check.
Do not treat a fresh clean worktree build as part of the closeout requirement
when it would trigger a cold dependency or mathlib build. Closeout should use
the active warmed worktree for targeted Lean builds plus the status/dashboard
and repository audit checks. A temporary clean worktree is acceptable only for
cheap committed-state checks such as generated metadata, `git diff --check`, or
status-sync validation, or when CI/public release work explicitly requires it
and the needed dependency cache is already available.
Do not run concurrent `lake build` commands in the same worktree: Lean cache
writes can race on `.olean`/`.ilean` outputs and produce spurious missing-file
failures. Prefer one targeted Lean build at a time, especially in shared
multi-agent sessions.
On Ubuntu-based systems where shell calls print
`Failed to create stream fd: Operation not permitted` before otherwise normal
output, prefer noninteractive command execution with no TTY and no login shell
when the tool supports it. In this Codex environment that means setting
`tty=false` and `login=false` on `exec_command`. Treat the warning as
environment noise only if the command's exit code and real output are clean.

When another agent will pick up later, spend tokens on durable artifacts rather
than chat: a paper-local handoff note, README/audit links, exact declaration
names, validation status, and next command. Future agents should start from
those files instead of reconstructing context from conversation history.
When reporting Codex token usage for a paper, workflow, or publication table,
avoid file-level overcounting. Parse only `~/.codex/sessions/**/*.jsonl`;
ignore prompt history files and plugin/test fixtures. In each rollout file,
the first `session_meta` is authoritative; later embedded `session_meta`
records may come from summarized context and must not overwrite the file's
identity. For unique-session counts, build a parent graph using
`source.subagent.thread_spawn.parent_thread_id` first and `forked_from_id`
second, then collapse to root session trees. Exclude guardian/auto-review
rollouts (`source.subagent.other = "guardian"` or model `codex-auto-review`)
from human formalization token tables unless explicitly reporting tooling
overhead. Report top-level/root-only usage separately from subagent-inclusive
actual API usage; do not mix a root session count with all-descendant token
totals without saying so. Subagent and resumed rollout files can embed a copied
parent transcript after the first `session_meta`; those copied records often
include parent `token_count` events and must not be charged again. For each
rollout, find the first own turn marker whose `turn_id` shares the session id's
leading timestamp group, then compute usage as the cumulative
`total_token_usage` after that boundary minus the last cumulative
`total_token_usage` before it. Cross-check that delta against summed
`last_token_usage` records after the same boundary. Cached input tokens are
already included in input tokens, so compute uncached input as
`input - cached`; charge reasoning tokens only through the output-token row. Do
not dedupe repeated parent/resume/subagent prompt context out of a
billable-usage estimate merely because a human regards it as repeated work:
each descendant model request still sends input tokens, and prompt caching only
moves matching prefixes to the cached-input rate. Replayed context in resumed
or subagent sessions is real API usage when it appears in the rollout's own
post-boundary usage logs, but if the goal is a human-facing "unique work"
estimate, label that separately instead of presenting it as raw billable usage.
For financial reconciliation, prefer the OpenAI Costs/Usage dashboard or Costs
API over local log reconstruction.
Sanity-check local counts against known scale. In the June 5, 2026 workshop
audit, `492` rollout files collapsed to `7` non-guardian root session trees.
The naive file-level sum over embedded transcripts reported about `$58k`; the
corrected post-boundary, subagent-inclusive non-guardian estimate was about
`6.05B` total tokens and `$4.6k`, with subagents contributing about `$775`.
If a future all-session estimate is an order of magnitude larger than the
top-level estimate, inspect for embedded parent transcript token events before
publishing the table.
When the latest green endpoint is a source-sequence, source-certificate, or
analytic boundary rather than the actual paper distribution/object, say that
plainly in the private handoff/plan and public status/final report. Name the
exact identification bridge still missing; do not let a compiled certificate
wrapper read like the paper theorem is fully closed.
For a pause of several days or longer, create or refresh a paper-local
`START_HERE_NEXT_AGENT.md` that is shorter than the full handoff: current
validation commands, shared-worktree caveats, the exact active proof seam,
strongest reusable endpoints, and what not to work on next. Link it from the
private paper README/plan and front repository status so a future agent has one
obvious startup path. Keep this handoff private by default; link it from the
audit/final-validation report only during a paper-done or user-requested
post-validation pass.
For a week-scale pause after a long proof push, also create a dated
paper-local handoff such as `HANDOFF_YYYY-MM-DD_WEEK_PAUSE.md` and make
`START_HERE_NEXT_AGENT.md` point to it first. That week-pause note should name
the exact current theorem seam, the strongest bridge theorem to use next, the
closed layers future agents must not redo, the files intentionally touched, and
the validation command set. Keep it concise enough to be read before opening
large theorem files.
If the latest green declarations are support endpoints rather than closed
paper results, say so explicitly in the handoff and do not over-mark the DAG.
If a paper is being paused for a stronger future model, say that explicitly in
the private handoff/plan and in the front repository status entries. Name the
three or fewer exact proof seams that remain and the strongest public wrapper
or certificate for each. Do not leave vague optimistic status such as "one
bridge remains" when multiple paper-level proof campaigns are still open.
When a remaining seam is a large family of repetitive row/table
identifications, package those facts into a source-shaped structure and expose
a single packaged bridge before stopping. Handoffs should point future agents
at the package as the proof target instead of asking them to rediscover a dozen
flat premises. Do not overclaim the packaged bridge as closing the source
model; say exactly which row-identification package is still unproved.
When bounded, Pareto, or other tail-heavy recommendation proofs duplicate the
same exact power-law finite-optimality argument, extract the FOC core into a
generic theorem parameterized by the marginal exponent, target exponent, and
exact backward/forward marginal formulas. Keep the distribution-specific files
as thin instantiations, and leave the source theorem rows `partially
formalized` or `conditional` until the probability/order-statistic derivation
supplies those exact or asymptotic marginals. Use `formalized with caveat` only
if the final theorem is closed but intentionally differs from the source
statement.
Do not derive a scaled first-difference/drop hypothesis merely from a value or
loss asymptotic such as `A - h(q) ~ C q^(-η)`. That asymptotic alone does not
control finite differences without a regularity/monotonicity theorem strong
enough for the source. If the proof needs `(q+1)*((A-h q)-(A-h(q+1)))/(A-h q)
-> η`, expose it as an explicit scaled-drop hypothesis or prove a separate
source regular-variation lemma.
For concrete bounded order-statistic laws, prefer a direct source-specific
mean-table route when it is available. An exact gamma-ratio formula for fixed
ranks can prove both the value/loss asymptotic and the scaled-drop law
internally, then feed the existing scaled-marginal certificate without exposing
`scaled_drop` to callers. Keep the reusable gamma-ratio asymptotic in the
library and the paper-shaped mean table in the paper unless another paper needs
the same table.
When a concrete iid source table is proved pointwise/top-`k` equal to a
synthetic mean table that already has asymptotic certificates, add or reuse a
small library-level certificate transport lemma rather than replaying the
asymptotic proof. For top-`k` order-statistic sources, the reusable pattern is
to prove the expected-order-statistic mean sequence equality, lift it to
top-`k` sums, and transport `ScaledMarginalLimitCertificate` through eventual
marginal equality.

Reserve `formalized with caveat` for cases where the Lean theorem adds
something on top of the paper statement, such as an extra assumption,
restriction, corrected statement, or indispensable source mismatch. If Lean
also proves that a broader arbitrary abstraction is false but the paper-facing
source theorem is closed, mark the paper theorem `formalized` and record the
broader abstraction as a scope note or out-of-scope failed generalization, not
as a caveat on the paper result.
Use `conditional` for an incomplete proof boundary: a wrapper still takes an
explicit certificate, witness, imported theorem, shortcut predicate, or
paper-model hypothesis that should be derived from the source assumptions. Do
not call this a caveat merely because Lean has not yet connected the paper's
own assumptions or appendix derivation. A caveat means the final theorem differs
from the source statement; a conditional status means the source statement may
be faithful but some derivation remains undischarged.
Use `partial_boundary` in assumption-provenance JSON for a visible external,
library, analytic, runtime, solver, or theorem-import boundary that remains
undischarged. This can be the top-level judgment for an `assumption_*`
declaration as well as an individual premise judgment. Do not downgrade it to
`documented_caveat` unless the source statement itself is false, missing a
needed non-source condition, or intentionally repaired in the Lean endpoint.
Use `documented_additional_assumption` for a non-source condition that a human
has approved as an additional-assumption note while keeping the paper status
formalized, such as an endpoint restriction that is recorded in the validation
report and explicitly marked non-caveat.
Use the following anonymous classification examples when deciding status and
report language:

| Situation | Classification | Public/report language |
|---|---|---|
| The printed theorem is false as stated, or Lean proves only a corrected/sign-repaired/constant-repaired endpoint that changes the source claim. | Real caveat; usually `formalized with caveat` if the repaired endpoint is closed. | "Paper issue/caveat: the source statement appears to need <repair>; Lean proves the repaired statement." |
| The paper/source model already implicitly or explicitly assumes the domain condition, such as positive capacity, more objects than slots, interior parameters, finite support, no ties, or a nondegenerate witness needed for an exact rather than at-most statement. | Not a caveat. Treat as a source theorem condition or source-model condition; use `paper_condition`, `source_text`, or `human_verified_source_implicit` in assumption/provenance sidecars. | "Additional/source condition: the theorem is stated with <condition>." Keep `main_caveat` blank if fully proved. |
| The user approves an extra non-source restriction while still calling the paper formalized, such as an interior-quality condition needed for a strict inequality where boundary cases are equality. | `documented_additional_assumption`, not `documented_caveat`, unless the user/source review says this is a paper error. | "Additional assumption: strict <claim> is proved under <condition>; this is recorded as non-caveat." |
| The source has a likely typo or finite-bound slip, but Lean proves the main asymptotic/source theorem through a corrected intermediate statement and the correction does not change the public theorem endpoint. | Source-quality note or proof-strategy deviation, not a paper caveat. | Put it under mathematical typos/source notes; keep status `formalized` and `main_caveat` blank. |
| An appendix/intermediate lemma is globally false as printed, but Lean proves the named theorem or main-text result by a different source-valid route, and also records the exact corrected local condition plus counterexample. | Source note, not a status caveat, unless the false lemma is itself the paper-facing target being claimed as-is. | Keep status `formalized`; write a short math note with the paper statement, actual Lean statement, counterexample, whether the condition appears elsewhere in the source, and how downstream theorems avoid or use the repair. |
| The source uses private data, empirical plots, implementation measurements, or descriptive program/class instantiations not needed for the mathematical theorem target. | Out of Lean theorem scope, not a caveat and not an additional assumption. | "Empirical/descriptive material is out of theorem scope." Do not list as remaining proof debt. |
| Lean currently assumes a solver theorem, convergence theorem, process law, runtime bound, certificate, source-record field, or bridge predicate that should be proved from paper primitives. | Proof/library boundary: `partial_boundary`, `conditional`, or `partially formalized` until proved. | "Full formalization requires proving <single boundary>." Do not call it a caveat unless the final theorem statement itself differs from the paper. |
| A converse, bridge lemma, or source derivation is missing but looks provable from the current source assumptions. | Missing proof debt. | Either prove it, or mark a proof boundary. Do not call it a caveat merely because it is not proved yet. |

For a user-approved axiom boundary, keep the axiom in the paper folder's
`Assumptions.lean` or another paper-local assumptions file, give it a precise
`assumption_*` name, and validate it as `partial_boundary`. Do not put
paper-specific axioms in reusable `EconCSLib/`, and do not hide paper formulas
inside a generic axiom that the recursive audit cannot identify.
Do not use `formalized with caveat` for source-quality notes, poor OCR, or an
audit observation that does not change the closed paper-facing theorem. Put that
note in the final report and leave the status `formalized`.
For such source notes, do not use `dag_caveat` styling or a caveat legend in
the dependency DAG. Keep the named theorem/lemma node in its ordinary
formalized style, mention the correction in concise paper-facing language, and
put the detailed statement/counterexample in the final report or a focused
math note.
When a fully proved endpoint exposes a standard regularity condition needed to
interpret a source formula (for example continuity/positivity needed for a
Laplace-principle reading), classify it as a validation note if the user/source
review accepts that reading and the Lean theorem does not leave proof debt.
Record the condition in `Assumptions.lean` and the assumption sidecar with
`paper_condition`, `source_text`, or `human_verified_source_implicit` premise
judgments as appropriate; do not mark it `partial_boundary` or
`documented_caveat` unless it is actually an undischarged theorem import or a
source-statement repair.
When the paper itself defines a convention that selects, erases, normalizes, or
packages terms, do not re-label that convention as a caveat merely because an
alternative raw mathematical object would differ. Close the source-shaped
statement, record the convention in an agent-facing audit note if future agents
are likely to confuse it, and keep the public status and human verdict focused
on whether the paper-facing theorem is closed.
For generated status files, keep `main_caveat` blank on clean `formalized`
papers. Do not put provenance summaries such as "axiom audit clean",
"assumptions source-matched", "human verified", or "no hidden premises" in a
caveat field. Those are validation/report notes, not caveats. Use
`main_caveat` only for a real source discrepancy, corrected statement,
indispensable non-source assumption, or explicit remaining boundary; otherwise
let the public table be sparse.
Before finalizing a public README, DAG, generated status surface, or validation
report, audit every `formalized with caveat` row. Run a focused grep such as
`rg -n "formalized with caveat|Formalized with caveat|dag_caveat|Caveat:"`
over the changed public paper/report/status files, then classify each hit. If
the issue is an unfinished theorem, external theorem import, runtime layer,
analytic derivation, missing library component, or other proof boundary that
does not change the final paper statement, use `partially formalized` or
`conditional` and describe the remaining boundary. Keep `formalized with
caveat` only when the closed Lean endpoint intentionally differs from the paper
because of an added non-paper assumption, a corrected/repair statement, or a
real source mismatch.
If any named source endpoint still exposes an explicit certificate, witness,
external theorem, or paper-model hypothesis that has not been derived from the
paper's primitive assumptions, the whole paper is `partially formalized`, even
if most theorem infrastructure compiles. It may still be public, but the README,
DAG, root status table, and final report must all name the exact remaining
certificate or external-library boundary.
If a paper-facing theorem genuinely needs a source assumption, expose that
assumption as a first-class declaration in paper-local `Assumptions.lean`
rather than as an arbitrary theorem hypothesis. Name it `assumption_*`,
`paper_assumption_*`, or `source_assumption_*`, list it in `status.json`
`review_surface.assumption_names`, and validate it in
`assumption_match_llm.json` with an independent source-assumption judge. A
premise is allowed to remain in a `formalized` endpoint only if it is routed
through that assumption ledger and the judge confirms it is an actual
paper/source model assumption. Capacity equations, threshold identities,
density normalizers, selection-mass formulas, row packages, and certificate
fields are proof obligations unless the paper explicitly assumes them.
Use the strict prompt sidecars when doing this validation. `lean_to_tex_llm.json`
should record
`prompt_version: "lean-to-tex-v3-strict-context-free-semantic-inputs"` and
preserve every binder, hypothesis, domain, named predicate/wrapper application,
direction, and conclusion in the translation; it must not turn a named premise
into a theorem label, source-like phrase, or proof-route summary. Each row needs
the current `lean_statement_sha256`; missing digests are stale audit evidence,
not optional metadata.
All model/agent audit sidecars are fail-closed. A blank scaffold, parse error,
missing file, missing current `prompt_version`, missing current digest, missing
validator/model identity, missing timestamp, stale source inventory, stale
dashboard surface, unrecognized judgment, failed run, or item without an
explicit success verdict is an alarm and does not count as audit evidence. The
only passing state is a current sidecar whose version, digests, validator
metadata, and recognized success judgment match the current Lean/source inputs.
Do not convert a missing or failed judge run into a warning merely because Lean
builds; Lean proves the encoded statement, while these sidecars audit whether
the encoded statement and visible assumptions match the paper.
At public-facing closeout, require an explicit current `review_surface_llm.json`
pass even for small dashboards. The 30-row threshold is an early workflow prompt
for broad human review, not an exemption from final review-surface evidence.
`statement_match_llm.json` should record
`prompt_version: "statement-match-v3-semantic-full-statement"` and reject
omitted source subparts, extra non-source hypotheses, hidden strengthening
inside named predicates, formula-level changes, broad aggregates, source-row
packages, certificate/replay/process/bridge packages, and any input whose
semantics does not match a paper primitive or a Lean-derived consequence of
paper primitives. The statement judge must inspect named predicates/wrappers
semantically; phrase overlap and source-looking Lean names are not evidence.
Each item needs current Lean, paper, and TeX statement digests.
For assumptions,
`assumption_match_llm.json` should record
`prompt_version: "assumption-provenance-v3-semantic-exact-premise-source"`. Every exact
`-- audit-premise:` entry needs its own `premise_judgments` row with either a
source location, a Lean-derived provenance judgment, or an explicit
partial-boundary/not-source finding; a declaration-level judgment alone is not
evidence.
For source-record provenance, `source_record_match_llm.json` should record
`prompt_version: "source-record-v2-semantic-boundary-inputs"`. The judge must
classify every boundary-shaped visible theorem input and every recursive field
from `source_record_audit.json`; a replay/certificate/process/bridge/source-row
input cannot be approved unless the sidecar gives specific source evidence, a
Lean constructor/derivation from primitives, an approved external boundary, or
an unresolved finding. Do not count old unversioned source-record sidecars as
current.
A `source_record_match_llm.json` entry classified as
`approved_external_boundary` is not compatible with a fully `formalized` paper
endpoint unless that endpoint is explicitly outside the claimed proof surface.
It is valid evidence for a partial/conditional row only after the same boundary
appears in `status.json`, the DAG, and the final validation report. If a
source-record audit separates bare witness data from a proposition-valued
validity or replay predicate, treat the bare witness as possible source-model
data and the validity/replay/process-preservation predicate as proof debt until
it is derived from paper primitives or recorded as the intentional partial
boundary.
Remember the visibility limit of the LLM assumption lane. It sees configured
`Assumptions.lean` declarations and exact `-- audit-premise:` rows; it does not
automatically certify arbitrary structure fields, library definition bodies, or
helper theorem premises excluded from the review surface. If a source formula is
encoded inside a record field or library definition, recursively inspect that
field/body or prove a paper-local equivalence before calling the premise
derived. If a theorem premise is outside the reviewed/assumption/auxiliary
classification, treat that as an audit failure, not as a harmless helper.
Check the expanded Lean signature, not only the source text of the wrapper.
Unused proof arguments and broad row bundles can print as anonymous top-level
arrows such as `SomeRows ... -> theorem_conclusion`, with no binder name for a
regex to catch. Premise checks must classify the head of each visible anonymous
premise type and either discharge it, route it through a named
`Assumptions.lean` declaration with `-- audit-premise:` comments, or mark the
endpoint partial/conditional. Prefer exposing the smallest component source
assumptions and constructing broad row bundles internally; do not leave a
single aggregate `PublicRows`/`SourceRows` premise as the paper-facing
provenance boundary when its fields are separately reviewable.
Keep the expanded dashboard cache current before using it as evidence: after
changing `PaperInterface.lean` aliases or theorem signatures, run
`python3 scripts/review_dashboard.py --paper <paper-folder> --refresh-cache`.
The expanded dashboard statement is the visible review surface for ordinary
scalar theorem conditions such as positivity, interval membership, or displayed
paper inequalities. It is not enough for certificate/source-row/external
boundary packages: those must still be constructed internally, exposed as
validated paper assumptions, or marked partial/conditional.
For analytic or algorithmic theorem boundaries, first construct the concrete
source-model record from visible paper primitives, then prove a bridge from
that record plus the theorem-shaped external axiom to the endpoint
consequences. Avoid axiomatizing the endpoint consequence package itself,
because that hides whether the paper's source semantics actually feed the
external theorem.
Do not rely on "source row" wrappers or theorem parameters to smuggle formulas
into a closed proof. A displayed formula, defining equation, threshold equation,
normalization, selection-mass identity, distribution law, recurrence, or
capacity condition counts as derived only when Lean proves it from the source
model primitives or it is listed as a source assumption and validated at premise
granularity. If such a formula is merely supplied to the theorem, the endpoint
is conditional/partial no matter how faithful the statement text looks.
This rule applies to every formula, not only admissions cutoffs or normal
integrals: signs, constants, denominators, support/domain restrictions,
normalizers, mixture equations, recurrence steps, equilibrium inequalities,
objective decompositions, and probability-law identities all need either a Lean
derivation from primitives or explicit source-assumption provenance.
This applies through the reusable library as well as paper-local files. A
library theorem may take an explicit certificate, witness, or formula package;
that is a good API because Lean forces callers to provide it. A paper-facing
row is closed when its expanded statement no longer exposes such a premise and
`#print axioms` on the row reports only approved standard foundations. Do not
mark a row partial merely because its proof calls internal library lemmas with
certificate-shaped names when those certificates are constructed by closed Lean
theorems. Do not bake paper-source displayed formulas into `EconCSLib/`
definitions or implicit instances to make the call site look unconditional;
make source formulas explicit parameters/certificate fields or keep them in the
paper folder.
If a reusable definition itself contains a formula that came from one paper,
the library audit cannot prove the formula correct by naming convention alone.
Make the library definition paper-neutral and expose the paper-specific
identification as a caller-supplied theorem/certificate or a paper-local
derivation. This keeps transitive dependencies honest: all source-dependent
facts used by a paper-facing theorem must either appear in that theorem's
expanded premise/provenance surface or be constructed internally from proved
primitives.
After editing reusable library code, run
`python3 scripts/audit_repository.py --library-only --library-premise-audit`.
This fails source-shaped reusable API names, hidden proof-boundary section
variables, axiom/opaque placeholders, and guarded debug commands, and reports
direct certificate-boundary APIs as informational findings. The
library parser covers theorem, lemma, def, abbrev, structure, class, and
inductive declarations; do not assume a proof-boundary structure is invisible
to the audit just because it is not a theorem. If the audit flags a
source-shaped reusable name, either rename it to a paper-neutral abstraction,
make the source formula an explicit argument, or move it back to the paper
folder.
Use `--info-limit -1` when you need the complete library-boundary inventory.
CI should use `--info-limit 0` so only actionable errors/warnings appear in
logs.
When private GitHub Actions fails but `gh` cannot read logs because local
authentication is stale, reproduce the workflow commands locally before
guessing at the failure: `scripts/sync_paper_status.py --check`, the
library-premise audit, and the relevant `lake build`. Run the full repository
audit only when the failure came from the manual closeout workflow path or the
user explicitly asks for closeout validation. Treat a clean local reproduction
as the basis for a scoped CI fix, and report that remote logs were unavailable.
Keep CI fast by separating metadata/workflow churn from proof changes. A
skill-only commit should not run full Lean CI; configure workflow
`paths-ignore` for `skills/**` and commit proof-affecting changes separately.
Use GitHub Actions `concurrency` with `cancel-in-progress: true` for Lean CI so
superseded pushes on the same branch do not burn a full build. In the workflow,
run fast source-only checks such as `scripts/sync_paper_status.py --check` and
the library premise audit before `leanprover/lean-action`; that fails status or
provenance drift before the expensive Lean build starts. Keep the full
repository closeout audit behind `workflow_dispatch`, not routine push/PR CI,
unless the branch is specifically being promoted or released.
Do not block your own work by watching GitHub CI unless the next action
actually depends on the result, such as merging a PR, cutting a public release,
or diagnosing a known failure. For routine pushes, confirm that the run started
or was intentionally skipped, record the run if useful, and keep working.
Treat suffix-named structures such as `...Certificate`, `...Oracle`,
`...Window`, `...Package`, `...Process`, `...Regularity`, and `...Invariant` as
proof-boundary evidence even when they are not named `hcert`. Do not keep these
as namespace/section-level `variable`s in reusable code; pass them explicitly to
each theorem/definition that consumes them so callers cannot inherit the
premise silently. Generic data predicates such as `feasible : α → Prop` or
`move : α → α → Prop` may remain section variables when they are just model
parameters, not proof evidence.
Apply the same visible-premise rule inside the paper folder. If a paper-facing
theorem, its expanded `#check` statement, or a direct paper-local alias target
still takes a certificate, hidden hypothesis, source-row equation, or
proof-boundary premise, that premise must be derived, routed through
`Assumptions.lean`, or marked partial/conditional. If a helper constructs the
certificate internally and the final paper-facing theorem no longer takes it as
an input, the certificate is discharged; confirm that with `#print axioms`
rather than a lexical dependency scan. Do not use `axiom`, `constant`,
`opaque`, or unsafe declarations to stand in for the missing derivation unless
the user explicitly approved one named theorem-shaped external boundary axiom
and the paper is reported as conditional/axiom-boundary. Even then, do not use
an endpoint-consequence axiom when a concrete source model plus an external
theorem statement would expose more of the real proof obligation.
Do not leave those proof obligations as the default proof shape. If an
explicit certificate, row package, or extra hypothesis is introduced to unblock
a build, treat it as a temporary checkpoint: immediately name the closure lemma
that would derive it from the source model, attack that lemma before moving to
new paper results, and keep the downstream theorem partial/conditional until
the certificate is either discharged internally or promoted to a validated
paper-assumption declaration. The normal proof loop should reduce the number of
visible certificates and extra hypotheses, not accumulate them.
For a final `formalized` paper, `scripts/audit_repository.py` should not report
hidden-premise, source-row, opaque-alias, broad-aggregate, stale-LLM-sidecar, or
missing-source-provenance findings for that paper's review surface. If the
global audit reports unrelated active-paper warnings, filter to the paper under
review and make the final claim only for papers whose own warnings are clean or
explicitly classified as non-theorem packaging notes.
If a certificate/interface structure is constructed internally and the final
paper-facing theorem no longer takes it as an input, that certificate is
discharged. Do not imply additional certificates are needed; for fully
formalized papers, status comments may be empty.
If a named paper theorem is closed but a downstream corollary or application
that uses it is still conditional, split the status/DAG entries. The named
paper theorem should stay green with its actual statement; the conditional
application should get its own row or node. Do not let a harder follow-on
endpoint make the source theorem look unformalized.

In EconCSLib, paper-local `papers/<Paper>/status.json` files are the source of
truth for paper status, compact `human_summary` notes, human-review row counts,
`PaperInterface.lean` metadata, review-surface slices, and artifact paths.
After changing any of that metadata, run `python3 scripts/sync_paper_status.py`
at a status milestone. That command regenerates the detailed
`papers/status.json`, the compact human-facing `papers/human_status.json`,
`docs/PAPER_STATUS.md`, the generated paper-status block in the top-level
`README.md`, and the status table in `site/index.html`. Do not hand-edit those
generated status outputs. The sync script defaults to tracked paper status
files so untracked draft scaffolds do not pollute generated CI-facing tables;
use `--include-untracked` only when intentionally syncing a new untracked
paper scaffold. During routine proof iteration, do not run the status sync just
because Lean LOC changed or a small proof seam was added; defer
generated table/doc refreshes until a named paper result closes, a status note
changes, a final report/handoff is prepared, or the user explicitly asks. If
README/docs/site/table text is wrong, fix the paper-local `status.json` and
rerun the sync script at that milestone. If a generated table needs
display-only publication wording that differs from local provenance, use
`papers/catalog.json` `publication_overrides` and leave paper-local
`source_version` fields as the source/provenance record.
If stale paper-local documentation or status is distorting the proof plan,
causing closed work to be rediscovered, or could lead a human to stop the right
proof campaign from an obsolete status belief, update the smallest paper-local
README/handoff/status fields immediately. Still defer repository-wide generated
README/docs/site/table refreshes until the next real milestone unless those
generated files are the misleading decision source.
Keep `sync_paper_status.py` metadata-only and fast by default. It should not
import dashboard code, run Lean previews, refresh LLM sidecars, or perform
closeout checks unless an explicit opt-in flag such as `--dashboard-audit` is
used. CI should run `scripts/sync_paper_status.py --check` as an early source
check; if that step times out or fails before Lean, first suspect stale
generated status or an accidental slow import in the sync path, not a proof
failure.
Use `human_summary` for the short public-facing note in generated tables.
Formalized papers should usually have an empty summary; add text only for a
reader-relevant source-version, proof-route, or caveat note. Human-review counts
mean saved dashboard rows by a human reviewer over the curated source-facing
review surface: `reviewed_rows / total_rows`. Do not use raw
`PaperInterface.lean` declaration counts as human-facing dashboard totals when
proof-support endpoints can be excluded with `review_surface.include_names`,
`assumption_names`, or `auxiliary_names`. Agent source audits, validation
reports, and compile checks do not increment human review.
Website status tables should expose human review and row-local
LLM-as-judge statement translation, not paper-level source coverage. Keep
paper-level source-inventory coverage in validation reports, audit JSON, and
`docs/PAPER_STATUS.md`; do not surface it as a public website table column.
For a partial or conditional public entry, make `human_summary` one concise
sentence: name the paper-facing results already closed and the exact remaining
external/library/model certificate. Avoid Lean declaration names, helper-layer
names, route history, and process words; a reader should understand the status
from the source theorem labels and the mathematical boundary alone.
If `status.json` includes `human_summary_review.status = "human_approved"` or
`"human_written"`, preserve the summary verbatim unless a human explicitly asks
for that summary to be edited. Automation may require a nonempty summary for
non-formalized papers, but it should not rewrite human-written or
human-approved prose merely to shorten, polish, or normalize it.
When doing an all-public-paper audit or syncing public status into the paper
or website, derive the paper list from the active public checkout's tracked
paper-local `status.json` files, `papers/human_status.json`, or the sync
script output. Do not rely on a manually remembered list of "public papers";
selected public partials are easy to omit, and private/in-progress papers are
easy to leak. Run the aggregate status sync in the checkout whose outputs will
be committed, because private and public aggregate tables intentionally differ.
If the command is run from the private incubator, still derive the public-paper
audit set from the sibling public checkout. A broad private `papers/status.json`
loop is useful for incubator triage, but failures on private-only papers are
not public-release blockers unless those papers are intentionally being moved
into the public repo.
If the user asks for DAG regeneration, commit, or push at the next milestone,
treat the milestone as a green named theorem seam plus the relevant targeted
builds and hygiene checks, not as every helper alias. At that milestone, refresh
only the affected DAG/status artifacts, inspect the rendered DAG if it changed,
stage an explicit path list, commit once, and push without adding a routine
rebase unless the user asked for one or a true publication/library milestone
requires it.
Do not churn status metadata during tight proof loops. Treat status syncs as
publication/checkpoint work, not as a per-build or per-proof maintenance step.
Update paper-local `status.json` and run the sync only at coherent milestones:
new scaffold intake, a theorem/status row changing, a review-surface change, a
final report/handoff/publication pass, or an explicit user request. For
ordinary proof edits, formula wrappers, small library lemmas, and compiler-fix
iterations, rely on targeted `lake build` checks and update status once the
batch has a stable boundary. This includes mechanical metadata such as
`line_count`, `declaration_rows`, `review_rows`, `total_rows`, and review-slice
lists: do not chase those counts after each interface helper or proof wrapper.
Let them be temporarily stale during active development and reconcile them in a
single pass at the next real review, report, commit, publication, or handoff
boundary.
If stale documentation or status metadata is actively distorting the proof
plan, causing the agent to redo closed work, or likely to make a human shut down
the right proof campaign based on obsolete status beliefs, update the smallest
paper-local docs/status fields immediately. This is a proof-planning fix, not
routine documentation churn; keep it narrow and defer generated aggregate syncs
unless the changed field is the aggregate source of truth for the current
decision.
Keep broader human-facing document churn low for the same reason. During an
active proof session, do not refresh READMEs, DAGs, final-validation reports,
website tables, or public status summaries for every helper lemma or small
interface wrapper. Batch those edits for real session boundaries,
publication/checkpoint milestones, explicit user requests, or roughly
once-a-day progress rollups. Short private scratch notes or paper-local
handoffs are still appropriate when they materially help the next proof step;
the constraint is on outward-facing documentation churn, not on useful working
memory.

When a proof is blocked, think outside Lean as needed, patch the mathematical
argument yourself, and then implement the patched proof in Lean. Do not stop at
identifying the gap unless the target theorem is false or the needed assumption
is mathematically indispensable.

If a paper proof is imprecise, think hard outside Lean to create a precise proof
strategy, implement that strategy in Lean, and record the issue in the live
README or handoff. Carry it into the paper's final report only during the
paper-done or user-requested post-validation pass.
If a paper's printed finite constant appears wrong or under-justified, separate
the exact finite claim from its downstream use. Prove and expose the corrected
finite bound with the constant Lean can justify; document the sharper printed
constant as a source deviation or conditional sharp bridge only if the exact
finite result is itself a named target. If later paper results only need a
vanishing/asymptotic bound such as `O(1/N)`, route them through the corrected
bound and say plainly that downstream consumers are unaffected by the finite
constant discrepancy.
Even when such a finite claim is a named theorem, lemma, appendix result, or
preliminary proposition, do not let an inessential sharp constant block the
paper's main theorem path. Prove the strongest corrected version justified by
the source and Lean, expose it under a name that signals the correction, and
document exactly how it deviates from the printed statement. Treat the printed
constant as an open sharp variant only when a downstream result genuinely
depends on that exact constant.

When the right proof strategy is unclear, think deeply outside Lean before
editing. If a written scratch argument would help, create a short `.txt`,
`.tex`, or `.md` sketch in the paper folder; keep it only as detailed as needed
to unlock the Lean proof. Do not create a sketch when it would be ceremony
rather than useful proof planning. After the strategy is clear, execute it in
Lean and keep moving.

If a proof loop has produced several wrappers, adapters, or public aliases
without shrinking the visible theorem assumptions, stop before adding another
layer. Write or update a short outside-Lean plan that names the current target
declaration, the theorem application that should close it, and classifies each
remaining visible premise as a source assumption, a derivable row/lemma, a
definitional surface mismatch, or a real semantic gap. Prefer proving the
missing row-identification lemma or choosing the right concrete source surface
over adding more wrappers. Resume Lean only after the plan names the next small
build target and why each exposed premise should be discharged, bundled, or kept.
For proof-facing certificates, "kept" is a temporary decision, not the default
end state: either prove the certificate constructor now, expose the premise as
a validated source assumption, or mark the exact source theorem partial. Do not
start a new theorem while the current theorem still has an easy-to-state
undischarged certificate or row hypothesis.
Treat wrappers as proof progress only when the final paper-facing theorem type
gets closer to the paper statement: fewer visible certificates, fewer unproved
row hypotheses, or a more faithful source surface. If an already-stronger
compiled endpoint exists under a secondary name, rewire/promote the public
paper-facing alias before adding new helper layers. Use `#check` or a temporary
scratch theorem to inspect the actual theorem type; do not infer remaining
work from long declaration names or README prose alone.
If `#check` shows that the remaining premises are exactly the paper's displayed
source assumptions, do not try to "prove" them away by inventing a stronger
model unless the paper claims that derivation. Treat them as legitimate theorem
inputs. If the remaining premises are source-model identification rows that the
paper derives in an appendix, make that row package the active proof boundary
and name it explicitly. For appendix restatements such as "Theorem N (Theorem
M)" or "Proposition N (Proposition M)", do not create a separate proof target
unless the appendix statement contains genuinely new conclusions; otherwise
map it to the main theorem/proposition endpoint and expose any extra appendix
parts as support rows only when they are paper-facing.
When a source theorem has logically independent assumption components, preserve
that separation through the proof-facing and paper-facing interfaces. Do not
reassemble a coarse older bundle merely to call an existing helper if one part
belongs to feasibility, another to a merit/objective inequality, and only the
coarse bundle makes the result look more conditional. Instead, add or use the
small adapter that consumes exactly the component needed by the current proof,
then feed the remaining source-shaped component to the theorem that actually
uses it.

When this outside-Lean diagnosis is needed, make it mathematical rather than
ceremonial. Read the local source TeX around the source theorem and proof,
write the intended paper route in a few bullets, then map every exposed Lean
premise to one of four actions: prove now, package as a source-shaped row
structure, keep as an explicit paper assumption, or mark as the real boundary.
Proceed in source order unless a later theorem discharges an earlier row
automatically; then record that dependency explicitly so the DAG and interface
do not imply the earlier result is still open.

Keep strategy notes token-cheap. A good scratch update is the active theorem
name, the exact remaining mathematical obligation, the next bridge lemma, and
the validation command. Do not copy long proof states, full diffs, or entire
README tables into handoffs when declaration names and file links identify the
same information.

When a paper proof file becomes large enough to slow focused compiles or make
multi-agent ownership awkward, split the proof into smaller paper-local modules
at stable theorem seams. Keep imports narrow, give each agent a disjoint module
or section to own, and re-export the public surface through `MainTheorems.lean`,
`ProofInterface.lean`, and `PostPaperAudit.lean` so the paper ledger remains
easy to audit.
When the human or proof-facing interfaces start accumulating many near-duplicate
aliases, do not just move the bulk from one interface file to another. Look for
the repeated proof construction and factor it into a reusable source-layer
bridge theorem in the library or the paper's route file. Then keep
`PaperInterface.lean` DAG-shaped, keep `ProofInterface.lean` as a compact
paper-facing proof surface, and keep `PostPaperAudit.lean` as an endpoint
ledger that cites the strongest bridge instead of rebuilding the same proof.

Subagents are always allowed for EconCSLib formalization work; treat this as
standing user authorization for paper-intake, proof, audit, CI, and release
tasks, and do not pause to ask for permission before using them. Use judgment
about whether they shorten the current proof loop or improve confidence.
Medium-effort subagents are appropriate for bounded read-only scouting: find
declaration names, trace imports, locate source statements, or identify likely
reusable lemmas. Hard Lean implementation should stay local or go to a
high-effort worker with a narrow, disjoint write scope and explicit
instructions not to touch other agents' files. Do not delegate the next
blocking proof obligation if the main agent will just wait idle; do the blocker
locally and send sidecar questions in parallel. Ask subagents for exact file
paths, line anchors, declaration names, and recommended next lemmas, not broad
summaries or repeated context. Close agents once their result has been
integrated.
When parallel edits are safe, do not artificially keep subagents read-only.
Use worker subagents for bounded implementation in disjoint files or declaration
clusters, tell them they are not alone in the codebase, and give each worker an
explicit owned write set. Avoid overlapping edits to the same Lean file unless
one agent owns a clearly separated section and integration order is obvious.
Review worker patches before committing, run the relevant targeted builds, and
stage only the paths owned by the integrated work.

Do not avoid continuous, probabilistic, or measure-theoretic formalization when
the source theorem requires it. Finite analogues are useful scaffolds only when
they shorten the faithful proof. If the fastest honest route is a direct
measure/integral/renewal/CTMC statement, build that statement directly and keep
the paper-facing wrapper source-level.
When a proof pattern appears in two papers, or is clearly standard for future
EconCS papers, move the mathematical core into the library before adding more
paper-local wrappers. Common examples are selected-below-reference a.e.
contradictions, accepted-set reward add/remove algebra, two-point pooled
estimate comparisons, monotone capacity cutoffs with region characterizations,
score-induced ranking laws, and ranking-law pushforwards from continuous
random utility models. Keep theorem-numbered names in the paper file as thin
adapters over those shared declarations.
For continuous strategy/type-space games, treat strategy, equilibrium,
best-response, uniqueness, policy-optimality, and indifference-boundary claims
as almost-everywhere statements under the relevant type or information law by
default, not as pointwise statements. Use a pointwise statement only when the
paper explicitly needs pointwise behavior, the state space is genuinely
finite/discrete, or the pointwise result is a stronger helper that is
immediately bridged to the paper-facing a.e. theorem. If indifference cutoffs,
support boundaries, or off-support types are null events, state the theorem
a.e. and prove separate boundary-null/no-atoms lemmas rather than adding
artificial pointwise tie behavior. Load
`references/proof-foundations-probability.md` for measure-zero/boundary-null
routes and `references/proof-mechanism-design.md` for Gaussian strategy-game
a.e. equilibrium patterns.

When Lean exposes a contradiction or apparently false source statement, do not
immediately mark the paper theorem false. Pause the Lean loop briefly: reread
the source PDF/TeX around the exact theorem and proof paragraph, think through
the intended mathematical statement outside Lean, write a short paper-local
proof plan, and then implement the repaired route. If the source really appears
to assert the false statement, surface that issue to the human before rewriting
the theorem status; otherwise treat the correction as a faithful formalization
repair and continue. Common repairs include replacing an over-strong pointwise
claim by a law-level or almost-everywhere statement, adding a missing
nondegeneracy/support assumption, separating a displayed formula from a
derivation-corrected formula, or weakening an auxiliary abstraction while
preserving the paper-facing theorem.

When source model assumptions are ambiguous, search beyond the local PDF before
deciding whether a Lean field is a paper convention or an extra certificate.
Look for public TeX/source archives, author-hosted PDFs, conference and journal
versions, and source repositories. Record when no public TeX/source is found.
Later versions may clarify conventions such as anonymity, tie-breaking, or
masked-vector models, but do not silently switch the paper target to a later
version. If the later version becomes the source of truth, update the paper
identity, theorem inventory, numbering, DAG, README, status rows, and final
report together.

Keep theorem-specific proof tactics out of this always-loaded file. Use the
reference routing table at the end: CTMC/reward-rate details live in
`references/proof-foundations-probability.md`; dynamic-game/PBE certificate
details live in `references/proof-mechanism-design.md`; market and social
choice details live in `references/proof-markets-social-choice.md`.
Do not present a finite source-event, finite schedule, trace/replay, or
strict-realized-profile equilibrium endpoint as a full continuous
type-distribution PBE theorem. Such endpoints can be useful source-facing
partial progress, especially when they expose the named strategy, exact trace,
and outcome/payoff equality, but the full source theorem remains partial until
the continuous type law, belief consistency, global PBE semantics, and
PBE-to-local-best-response bridge are formalized or explicitly approved as a
boundary. If a continuous theorem is reduced to a local best-response
certificate, keep that certificate out of the fully formalized status unless a
Lean constructor derives it from the continuous source game.
When updating the skill, treat this as an invariant, not a preference: if the
new lesson names a specific paper, theorem number, counterexample, proof
recipe, or declaration family, it belongs in a reference file unless it is only
a one-line routing pointer.

When a displayed formula conflicts with its surrounding derivation, do not
silently overwrite the paper statement. Keep the literal source formula and the
derivation-corrected formula as separate named definitions or wrappers, prove
the corrected bridge from the surrounding source equations when possible, and
record the discrepancy in the paper handoff during active work and in the final
report during post-validation. Only mark a paper-facing theorem as closed for
the exact statement Lean actually proves.

For rounding, discretization, PTAS, or finite-search proofs, track scale changes
explicitly. If the source rounds values using one baseline scale but defines a
new average, budget, or normalization after rounding, do not force an exact
normalization back to the original scale. Build a two-scale interface: one
parameter for the value grid and a separate parameter for the rounded
instance's average/window, plus the finite count-cap or boundedness lemma that
makes the search space finite. Keep any one-scale theorem as a clearly marked
staging lemma until a source-faithful two-scale bridge exists.

When starting a new paper, briefly inspect the repository's already-formalized
papers in the same EC area and ask which proof moves should become general
library tools. Do not force a detached library project before proving the paper,
but if a lemma, interface, or theorem is likely to be useful to another EC paper,
build it in `EconCSLib` while formalizing the current result.
When a proof needs the "top `k`" elements of an arbitrary finite profile, prefer
building a ranking/top-prefix interface on the original domain over reindexing
the whole mechanism. Reindexing is often harder because selected argmaxes,
sampled subprofiles, or chosen witnesses may not be definitionally equivariant;
a source-shaped top-prefix family usually preserves the paper argument with
less transport machinery.

When starting a paper or beginning a serious paper audit, do an extended
outside-Lean paper sanity pass before deep Lean implementation. Read the local
source cache, inspect every named result and formula-bearing displayed claim,
and ask whether the signs, constants, normalizations, quantifiers, domains, and
proof dependencies look mathematically correct. Separately think through the
formal proof strategy: the main theorem chain, likely reusable library seams,
underspecified paper steps, necessary assumptions or certificates, and fallback
proof paths. Write these initial learnings in `FORMALIZATION_PLAN.md` under an
`Initial Outside-Lean Paper Audit` section before proving. Treat this as a
hard start gate, not an optional narrative note. Use
`templates/FORMALIZATION_PLAN.md` as the section/checklist template when
creating or refreshing a paper plan. The plan must explicitly contain:

- source/version inventory: official source, open/cached source, local PDF/text
  cache paths, and any source mismatch between publication versions;
- source theorem ledger: every named definition, proposition, theorem, lemma,
  corollary, algorithm, and theorem-like displayed formula that could become a
  Lean review row, with source locations when available;
- formula/dependency sanity pass: signs, constants, denominators,
  normalizations, quantifiers, domains, density-vs-mass interpretation, and
  which earlier paper objects each result depends on;
- shared-library reuse checkpoint: mathlib/cslib/optlib/EconCSLib modules or
  declarations inspected, the API chosen, and near-misses that explain any new
  reusable library definitions;
- formal target map: which source rows will be fully proved now, which rows are
  empirical or out of theorem scope, and which candidate boundaries would be
  explicit assumptions/certificates if the paper cannot be closed immediately;
- execution checklist: concrete start-to-closeout tasks for source intake,
  reusable-library work, scaffold replacement, proof closure or downgrade,
  status/DAG/report updates, audits, and unresolved source/library debt.

Use `.txt`/`.tex` only when that is genuinely more convenient for a detailed
derivation, and link or summarize it from the plan. Keep the artifact
functional rather than polished: it is a scratchpad for thinking and early risk
detection. If this pass finds a likely source bug, missing assumption, formula
ambiguity, continuous-density encoding issue, or strategy-changing issue, alert
the user early instead of silently encoding the printed formula as a source
row. Then start executing the plan in Lean. As the formal proof progresses,
edit the plan to record strategy changes, patched source gaps, discharged seams,
and remaining blockers.
For a post-validation or post-formalization audit pass, keep
`FORMALIZATION_PLAN.md` as the working scratchpad unless the user explicitly
asks to retire it. Put the durable human-facing audit in a separate paper-local
artifact such as `POST_FORMALIZATION_AUDIT.md`, `SOURCE_AUDIT.md`, or
`FINAL_VALIDATION_REPORT.md`. The audit artifact should distinguish publication
venue from the exact formalized source version, list source-named results with
statuses, summarize DAG and review-surface checks, and record library
extraction outcomes plus any deferred extraction candidates.
For public-release or public-paper audit passes, add a short outside-Lean
source-reasoning report for each paper, or a single rollup with one section per
paper. That report should say what source formulas/results were sanity-checked,
which possible issues were considered, whether each issue is already caught by
Lean/status/assumption/statement audits, and which issues remain uncaught by
the existing workflow. Treat uncaught issues as workflow bugs: either add a
generic checker, add a required review-surface row, or explicitly document why
the issue cannot be mechanically checked. Also check that
`FINAL_VALIDATION_REPORT.md` whole-paper verdict lines agree with
`status.json`; stale report prose is documentation drift even when the
machine-readable status is correct.
During that initial planning pass, also identify defensible partial
formalization boundaries. For each candidate boundary, say which named results
would be fully closed, which source assumptions or analytic layers would remain
explicit, why the boundary is scientifically useful, and what later work would
turn it into a fuller formalization. Surface those options to the human user
early and ask for their thoughts before committing to a long proof route.

For long or fragile proofs, keep a theorem-specific scratch plan beside the
paper files and use it actively, not as decoration. A good plan records current
Lean endpoints, the exact mathematical gap, the next two or three bridge lemmas,
why each bridge should be true, and which assumptions are source assumptions
versus temporary certificate fields. Put domain-specific certificate patterns in
the relevant proof reference file, not here.
When a long session ends before validation, write a paper-local handoff note
before stopping. Include the files touched, the latest unvalidated theorem
families, the intended proof route, exact next validation command, and likely
fragile Lean points. Link that handoff from the private paper README/plan so a
future agent does not need chat context. Do not publish that handoff or update
the post-paper audit report/final validation report for this intermediate stop
unless the paper is done or the user explicitly requested post-validation.
After validation succeeds, immediately update the handoff/status language from
"unvalidated" to the exact command that passed. Do not leave stale caveats that
force the next agent to rerun work just to learn whether the current additions
compile.
For dynamic-game, PBE, strategy, payoff, or schedule-certificate proof details,
load `references/proof-mechanism-design.md` instead of putting theorem-specific
guidance here.

Follow the original paper's proof structure as closely as is practical. Preserve
named definitions, lemmas, propositions, and theorem numbers in Lean declaration
names, docstrings, and status rows. When deviating from the paper proof
because Lean needs a reusable intermediate lemma or a cleaner finite/discrete
interface, make the deviation explicit and keep the paper-facing wrapper close
to the original named result.

When a source proof explicitly routes a theorem through named paper lemmas or a
named proof-line corollary, prefer formalizing that named route when it is
reasonably available. Do not spend unbounded time following the exact proof line
by line if a different or more precise argument proves the same paper-facing
statement cleanly. In that case, keep the named theorem/lemma structure in the
README, DAG, audit wrappers, and declaration names where practical; state the
same theorem; and record the route change in the live README/handoff. During
the paper-done or user-requested post-validation pass, carry it into
`FINAL_VALIDATION_REPORT.md` under `Proof-Strategy Deviations`. Do not replace
a named-lemma path with a looser certificate, alternate theorem, or broad
abstraction unless the resulting paper-facing endpoint still states the source
result or the source route is false, imprecise, or genuinely inapplicable. If
an auxiliary certificate is temporarily useful, keep it as a clearly marked
staging device, then immediately pursue the constructor/elimination proof that
removes it from the paper-facing theorem. A certificate endpoint is useful
scaffolding only if the next proof steps are closing it or proving downstream
results that do not depend on it being assumed.

For stable-matching/deferred-acceptance papers, load
`references/proof-markets-social-choice.md` after the first status pass. It
contains the matching-specific assumptions, strict-preference notation checks,
DA infrastructure guidance, manipulation-rank warning, and source-repair notes.

For STV/RCV, ranked-choice voting, Thiele, or multi-member district papers,
load `references/proof-markets-social-choice.md` before building paper-local
models. Start with reusable voting semantics under
`EconCSLib/SocialChoice/Voting`, then keep paper folders as source-versioned
thin wrappers and explicit empirical/simulation-boundary ledgers.
Before adding any new STV/RCV simulator, generated trace, full-election-run,
candidate-removal runner, Algorithm A/3/7 checker, or concrete algorithm type,
search the existing voting library and same-domain paper folders first. In
particular, inspect the GGRS RCV development and its imports, plus DGJ24/DGJ26
shared declarations, for `STVTrace`, `generatedTrace`, `replaysFrom`,
`minimalGroupElimination`, `canonicalProfileGroupElimination`, and
source-run/checker APIs. Reuse or thinly wrap that machinery unless the plan
records a concrete reason it cannot express the source algorithm.

For papers with computational-complexity, hardness, approximation-hardness, or
randomized-class claims, load `references/proof-algorithms-complexity.md` after
the first status pass. It contains the workflow for separating Lean-checked
reductions and solver transfers from external machine-level class semantics.

### 1.2 Library Layering Rule: Textbook vs. Audit Trail

Think of the repository as having two distinct roles: **`EconCSLib` is the textbook. The `papers/` directory is the audit trail.**

- **`EconCSLib/` (The Textbook):** Put generic, abstracted EC/CS/econ results here. If a definition, algorithm, or theorem is foundational enough that a graduate student should know it, or if a second paper might build on it (e.g., Gale-Shapley, Nash equilibrium, LP duality), it belongs in the core library.
  - **Abstraction:** Code here should be highly abstracted and stripped of
    paper-specific notation. Use generic types (`α`, `β`) and follow
    `skills/lean-community-conventions/SKILL.md` for reusable API naming,
    style, and documentation.
  - **Ownership:** Main library modules own reusable primitives: allocations, valuations, mechanisms, rankings, PMFs, finite expectations, graph/path lemmas, and generic algorithm correctness patterns.

- **`papers/` (The Audit Trail):** Each paper-specific folder is a formalization artifact proving that the specific claims in a specific PDF are true.
  - **Notation Fidelity:** Translate paper-specific notation (e.g., exactly matching the paper's index variables like `u`, `j`, `t`) into the shared primitives.
  - **Paper-Facing Wrappers:** Write theorems whose signatures match the paper *exactly*. These should be thin wrappers that call the generic library theorems. (e.g., `theorem roth82_theorem_1 : ... := EconCSLib.Markets.Matching.da_is_stable`).
  - **Local Ledger:** Keep the paper's specific narrative flow in `MainTheorems.lean`, `README.md`, and `DependencyDAG.tex`.
  - **Upstreaming Workflow:** It is normal to build everything inside a `papers/` folder initially. Once a proof is stable, **upstream** the generalized math into `EconCSLib`, leaving only the thin wrappers and paper-specific stepping stones behind.

- **Standard for Upstreaming:** To prevent "upstream bloat," use the "Second Paper" test: **Move a result to `EconCSLib` if a second paper or another likely EC formalization would plausibly need it.** Foundationally reusable math (like Gale-Shapley, Nash equilibrium, LP duality, threshold mechanisms, monotone single-parameter allocation consequences, or finite-expectation/probability interfaces) passes this test; hyper-specific algebraic lemmas or messy intermediate steps used only for one paper's specific narrative should remain in that paper's folder.
- If two papers could use a lemma after renaming variables, it belongs in the generic library.
- If a proof starts with a paper-local lemma and it becomes generic, extract it before building more paper-specific code on top of it.
- It is fine, and often faster overall, to create reusable library material while proving a paper when the abstraction directly closes the active paper seam and is likely to serve the broader EC community. Avoid speculative polish, but do not avoid general infrastructure just because the current paper could be hacked locally.
- In a multi-paper extraction pass, classify each lifted declaration before
  committing: already cross-paper, future-facing generic, or paper-local wrapper
  that should remain as audit trail. Do not expect paper LOC to fall in direct
  proportion to library LOC; source-facing theorem names, status rows, and thin
  adapters should stay in `papers/` even when the proof body moved. The useful
  cleanup signal is repeated proof construction replaced by shared imports and
  one-line adapters, plus green builds for all papers that import the lifted
  API.
- After a library extraction pass, update the discoverability surface before
  calling the pass complete: the reusable module docstring, any aggregate import
  docstring, `docs/ECONCSLIB_DOMAIN_INDEX.md`, and the relevant roadmap or
  extraction-plan index. Update this skill when the extraction creates a new
  workflow rule or a module future agents should check first.
- During library provenance refactors, avoid ambiguous pairs where a local
  package theorem and a full-order/source-facing package constructor share the
  same Lean declaration name. Use distinct paper-neutral names for different
  abstraction levels, such as local window versus full-order window, so the
  build and downstream wrappers cannot silently call the wrong package.
- Reusable library theorems may require explicit certificates, witnesses,
  external-boundary hypotheses, or source-shaped row packages from their
  callers. This is often the right API because Lean then forces every paper
  wrapper either to construct the certificate or remain conditional. Do not ban
  such library certificates. Instead, never mark a paper theorem `formalized`
  while the paper-facing wrapper still exposes the certificate unless that
  certificate is a validated paper-source assumption. During closeout and public
  PR preparation, run
  `python3 scripts/audit_repository.py --library-only --library-premise-audit` and inspect any
  library certificate/source-boundary APIs used by completed paper wrappers.
  This audit builds a fresh in-memory declaration index each run and reports
  direct certificate/source-boundary APIs and source-shaped reusable names; it
  should not be replaced by a checked-in index. Use it with the paper-facing
  `#print axioms` audit and expanded-statement review rather than as a
  substitute for Lean's dependency information. When extracting to the library,
  use generic definitions and explicit certificate parameters; avoid
  paper-specific formula constants, implicit certificate parameters, implicit
  instances, or names that make a source formula look like a generic theorem.
  For standard mechanism-design facts such as VCG truthfulness, an explicit
  certificate predicate may be the reusable definition of a VCG-style
  mechanism. Do not remove that binder unless the library already provides a
  concrete mechanism plus a Lean-checked constructor for the certificate; if no
  constructor exists, keep the binder visible and classify it as a source/library
  abstraction or partial boundary according to the paper's status.
- Reusable `Assumption`/`Hypothesis` declarations are not allowed in
  `EconCSLib/`; true paper assumptions live in paper-local `Assumptions.lean`.
  Shared modules should describe generic mathematical APIs, not paper/source
  provenance. When adding a standard-name wrapper such as a convexity,
  concavity, order, metric, or probability notion, add a build-checked theorem
  in `EconCSLib.LibraryDefinitionAudit` showing equivalence to the mathlib or
  local canonical definition, and keep that module imported by `EconCSLib.lean`.
- After a reusable-library provenance refactor or API rename, run a targeted
  validation matrix before calling it done: `rg` for stale old names, build each
  touched library module, build downstream paper libraries that import the API,
  and then build aggregate `EconCSLib`. If the refactor changes a heavily used
  generic certificate API, also build at least one representative downstream
  paper that exercises dot notation and paper-local adapters for that API.
- For domain-specific proof seams, use the proof-reference routing table below
  instead of adding theorem-family details to this always-loaded workflow file.
  The relevant reference should name reusable modules and declarations that
  future proof agents should check first.
- For LP-heavy papers, prefer a paper-local equality-form, certificate, or BFS-witness interface when that is enough to follow the paper proof and close named results. Build a generic LP/simplex/duality layer only when the current theorem truly needs it or a second paper will immediately reuse it; otherwise keep the optimization boundary narrow and auditable in the paper folder.
- Keep paper-module imports as narrow as practical. Avoid importing aggregate
  roots such as `EconCSLib` from paper-local proof files when a leaf module like
  `EconCSLib.Foundations.Probability.FiniteExpectation` or
  `EconCSLib.Foundations.Math.FiniteSigns` suffices; aggregate imports can make
  targeted paper builds depend on unrelated dirty library areas such as auctions.
  When narrowing imports, add the exact missing leaf import at the file that uses
  the declaration rather than restoring a broad root import.
- Treat a focused paper build that unexpectedly compiles unrelated library
  areas as an import-hygiene signal before debugging those unrelated files.
  Identify the declaration owner with `rg`, import that leaf module directly,
  and re-run the targeted `lake build Paper.Module`; do not broaden imports just
  to make the immediate elaboration error disappear.
- When a focused paper build fails in a shared library file that was not touched
  in the current task and other agents may be active, wait about one minute and
  rerun once before intervening. If the same shared-library failure persists,
  patch the minimal local problem yourself, rebuild, and move on; do not leave
  the paper blocked indefinitely on likely concurrent shared-library work.
- If the failure is `failed to open file ... .olean: No such file or directory`
  immediately after Lake claims the dependency was built, treat it first as
  shared build-artifact churn. Check for active `lake`/`lean` jobs with `ps`,
  let concurrent local builds finish, then materialize the missing dependency
  target directly (for example `lake build EconCSLib.Foundations.Probability.BivariateGaussian`)
  before rerunning the paper target. Do not debug theorem code until the same
  paper module reaches elaboration and reports an actual Lean error.
- After adding a declaration to an imported paper module and exposing it through
  `PaperInterface.lean`, rebuild the imported module or the paper target before
  relying on `lake env lean PaperInterface.lean`; direct Lean checks can read
  the previous `.olean` and report a false unknown-identifier error for a fresh
  public alias.
- For compile-repair passes, let the first `lake build PaperName` produce the
  error queue, then patch the first coherent cluster of errors by line number.
  Do not inspect the whole theorem file. Constructor-pattern errors are often
  fixed by checking the inductive declaration and matching only explicit
  constructor parameters; field-projection errors are often fixed by projecting
  from the certificate wrapper rather than an embedded base model.
- When committing from a dirty multi-agent worktree, stage only explicit path
  lists. Use `git status --short -- path...` and `git diff --stat -- path...`
  before staging. If Git cannot create `.git/index.lock` because another agent
  is using Git or the filesystem is temporarily read-only, pause; once clear,
  retry the same scoped path list. Never use broad `git add .` in this repo.
  Do not use `git reset` to repair staging or commits in a shared worktree;
  it can move or unstage other agents' work. Do not use `git restore`,
  `git restore --staged`, checkout-based file rewinds, or any "restage the
  index" recovery workflow in a dirty shared worktree; these can silently
  disturb another agent's staged or unstaged files. If a commit accidentally
  includes extra work, prefer a follow-up corrective commit, an explicitly
  scoped new commit for the remaining owned files, or direct coordination with
  the user/other agent. If unrelated paths are already staged, commit your
  owned paths with an explicit pathspec, e.g. `git commit -m "..." -- path1
  path2`, so the unrelated staged entries remain untouched. Normal first-time
  `git add path...` of files you just edited is fine; index surgery to repair
  mistakes is not.
- For private checkpoint commits on an unfinished paper, do not refresh
  aggregate paper status, global site tables, or unrelated paper audit sidecars
  merely because one paper changed. Run
  `python3 scripts/private_paper_checkpoint.py <paper-folder> --include-path <shared-path>`
  with every shared library/script/skill file that belongs in the commit; the
  helper includes the paper folder and root paper module automatically. Then
  stage only the command's printed path list. Commit paper-local
  `status.json`, source-record sidecars, dashboard sidecars, and final-report
  notes only for the selected paper unless the user explicitly asks for a broad
  status/audit refresh or a public-release handoff.
- Before editing a paper lane, identify which repository you are in and which
  paper set it exposes. Typical local sibling names are `EconCSLib-private`
  for the public-based private incubator and `EconCSLib-public` or
  `EconCSLib` for the public release repository. Older standalone private
  history belongs in the archive repository. Confirm with `pwd`,
  `git remote -v`, and `find papers -maxdepth 1 -type d | sort`; do not infer
  privacy from the repository title alone.
- Treat any older `EconCSLean` checkout as a legacy private working copy unless
  the user explicitly says otherwise. If it points at the same
  `EconCSLib-private` remote, do not start new work there by default; inspect it
  only to recover or migrate old dirty changes, then continue in the canonical
  `EconCSLib-private` or `EconCSLib-public` sibling. If `EconCSLean` is dirty,
  consider it a migration queue, not a backup and not an automatically synced
  source of truth.
- Route paper work by public status. If the requested paper exists only in the
  private incubator, do the work in the private repo unless the user explicitly
  asks to publish it. Do not add private paper rows, DAGs, reports, titles, or
  source material to public-facing docs without explicit approval. If the
  requested paper exists in the public repo, use the public repo as the primary
  worktree for public contributions and update only that public paper folder,
  its root module, reusable public library files, and public status/docs.
- In the private incubator, default to working and committing on private `main`;
  do not maintain private topic branches unless the user explicitly asks for one
  or there is a concrete isolation need. If a private branch already exists for
  routine paper work, merge its committed history back into private `main` at the
  next clean checkpoint instead of leaving it open. Use separate topic branches
  for public PR preparation in the public repository, not as the normal private
  workflow.
- The canonical private incubator is public-based: its history should remain an
  easy descendant of public `main` plus private paper commits. Rebase the private
  main branch onto public `main` only when a substantial public change matters
  to private work, especially library/API, generated-status, workflow, or CI
  changes, when a paper is finished, or before preparing a public PR. Routine
  private proof commits and checkpoint pushes do not require a rebase. It is
  allowed and usually preferred to push private `main` as-is after a normal proof
  checkpoint; do not treat pushing itself as a rebase trigger. Batch
  rebases at major proof/status milestones, such as when a paper is finished, or
  when the user explicitly asks. Do not rebase private after every small
  public-only documentation commit. After an intentional private rebase, push
  with `git push --force-with-lease origin main`; never use a blind force push.
- When a paper exists in both private and public, choose one primary worktree
  for the current task and keep all builds, dashboard refreshes, reports, DAGs,
  and commits in that same repo. Use the public repo as primary for public
  partials, external-contribution work, and pull-request preparation. Use the
  private repo as primary for unpublished papers, private planning, or work
  that may expose not-yet-approved paper content. Mirror between repos only as
  an explicit, path-scoped sync step; never assume that editing one sibling
  automatically updates the other.
- For a brand-new paper, default to the private incubator unless the user says
  the paper should be public from the start. Starting privately preserves
  exploratory history, failed proof plans, local source caches, and unfinished
  assumptions without exposing them. If the paper is a classic/public benchmark
  or an already-approved public contribution, it may start directly in the
  public repo. In either case, create the standard paper folder and root module
  in that primary repo, keep reusable paper-independent lemmas in `EconCSLib/`,
  and only move the paper to the public repo after its status is either
  `formalized`/`formalized with caveat` or an explicitly approved
  `partially formalized` public seam.
- When a filtered public repository sibling is being maintained, mirror
  public-safe formalization artifacts and skill updates there in the same
  checkpoint: README/status rows, concise final reports, DAG sources/rendered
  DAGs when tracked, review-slice configuration, scripts needed by the public
  review workflow, and the detailed public skill bundle. Keep private incubator
  folders, unpublished paper attempts, and private planning surfaces out of
  public diagrams and public-facing status text.
- When publishing work that was developed in the private incubator, do not raw
  merge, cherry-pick, or push the private branch into the public repository.
  Create a new public branch from current public `main`, then apply only an
  allowlisted patch from private. The allowlist should name exact shared-library
  paths, exact already-public paper folders, public workflow/skill/template
  files, and generated public status/site files. In the private repo, commit
  only the public-paper/workflow/skill paths requested by the user; leave
  unpublished paper folders and their generated/private status deltas out of
  that commit. In the public repo, regenerate aggregate status files from the
  public checkout instead of copying private aggregate tables wholesale. Use a
  binary/full-index patch for PDFs, for example
  `git diff --binary --full-index public/main..origin/main -- <allowlisted paths>
  --output=/tmp/public-filter.patch`, then `git apply` it in the public
  checkout. Do not include source-paper PDFs, extracted source-paper text
  caches, or unpacked source archives in a public-PR allowlist, even when the
  paper folder itself is approved for public partial release; reports should
  cite the source URL and describe local ignored caches instead. Before
  committing, inspect `git diff --name-only main..HEAD` and reject the branch if
  any private paper folder, private-only plan, source cache, scaffold row, or
  unpublished status entry appears.
- Public-release leakage checks must be path-sensitive. Grep the changed public
  surface for private paper identifiers, private paper titles, and new scaffold
  IDs. Existing historical mentions outside the changed path set do not justify
  new leakage. Regenerate public status from paper-local
  `status.json`, run `python3 scripts/sync_paper_status.py --check`,
  `python3 scripts/audit_repository.py`, placeholder scans on changed Lean
  paper folders, and the relevant `lake build` targets before pushing. When the
  filtered branch is approved, fast-forward public `main` to that audited
  commit rather than redoing the merge from private.
  If public or private CI fails in the status aggregate step before Lean, treat
  it as a generated-status consistency failure: rerun
  `scripts/sync_paper_status.py --check` in the exact checkout whose CI failed,
  regenerate status there if needed, commit the generated outputs from that
  checkout, and push. Do not copy aggregate tables across the private/public
  split or infer a theorem/proof failure from a pre-Lean status check.
- Public promotion audits should run both statement and assumption validation
  for every public paper row, including intentionally public partial papers.
  Conditional-boundary rows are acceptable only when the same boundary is named
  in the paper-local `status.json`, statement/assumption sidecars, README or
  validation report, and DAG if the row appears there. Do not "fix" an
  intentional conditional result by weakening the table text to look fully
  formalized, and do not treat a public partial as invisible just because it is
  not a finished paper.
- Before moving work from a private incubator into the public repository, run a
  release-hygiene pass. Public commits should not contain source-paper PDFs,
  extracted source-paper `.txt` caches, unpacked publisher/arXiv source
  archives, ignored dashboard caches, or private/in-progress paper rows unless
  the project intentionally publishes that partial formalization. Planning,
  proof-plan, handoff, audit, and citation-provenance `.txt` notes are fine to
  track when they are written by the project and do not reproduce the source
  paper text. Use `git ls-files 'papers/*/*.txt'` and `git check-ignore -v`
  before public commits if the distinction is unclear.
- Public partials are acceptable when their remaining seams are valuable and
  explicit. Do not hide partiality by publishing an all-green DAG, an empty
  caveat column, or a final report that only says the code compiles.
- After any broad library-extraction or paper-thinning pass, run a preservation
  audit before declaring the pass done. Compare the current private repo against
  the archive or the pre-extraction ref used for recovery. Check that no
  archived paper folder disappeared, no archived `.lean` file disappeared, and
  any large paper-local LOC drop is explained by wrappers moving to
  `ProofInterface.lean` or reusable library modules, not by deleting proof
  declarations. If `PaperInterface.lean` was thinned, every removed archive
  declaration name must either still be declared elsewhere in current Lean code
  or point to an underlying target declaration that still exists. If a removed
  interface alias cannot be resolved this way, treat it as proof-surface loss
  and restore or deliberately replace it before committing.
- Preservation audits must compile the actual private paper targets, not only
  the default public aggregate. Explicitly build every private/in-progress
  paper target and any new scaffolds when they are part of the pass. Strip
  comments before scanning for actual `sorry`, `admit`,
  `axiom`, or `unsafe` tokens; do not count ordinary arithmetic `by omega` or
  prose comments as proof gaps. Push private and public remotes only after both
  the content-preservation check and the relevant builds/audits pass.
- Before inviting broad public contributions, keep the public repo's legal and
  contribution surface explicit: code is released under the chosen repository
  license, currently Apache-2.0, while cached source PDFs/text extractions may
  be omitted or treated separately for source-publication licensing reasons.
  Maintain issue templates for new paper formalizations, statement mismatches,
  external certificate boundaries, library-upstreaming candidates, and dashboard
  review requests.

### 1.2.1 Paper Link Intake Protocol

When the user provides only a paper link and asks for autonomous
formalization, execute the standard intake before deep proof work:

- Download/cache the exact source PDF locally in a new or existing
  `papers/[AuthorInitials][2DigitYear][Descriptor]/` folder, then create an
  adjacent source-text extraction with `pdftotext` for search. Treat the PDF,
  extracted source text, and unpacked TeX/source archive as local reference
  caches: useful for proof work, but not public repository artifacts unless
  redistribution rights have been checked. In public checkouts, source-text
  caches should be ignored; do not commit them just because `pdftotext` made
  proof search easier.
- Download the published-version BibTeX into `citation.bib` during intake.
  Prefer the official published-source citation export, such as a publisher,
  conference, OpenReview, or journal site. Do not use arXiv BibTeX when a
  published version exists. If the official export is unavailable, use Google
  Scholar. If Scholar is blocked or unavailable, use OpenAlex as a backup to
  locate the exact published record, then use a real BibTeX export/translator
  for that record; OpenAlex JSON alone is not a BibTeX source. Do not
  hand-write or repair BibTeX metadata. Record provenance in
  `citation_source.txt`.
- If the paper link is arXiv, also download/cache the arXiv source archive
  (`e-print`) during intake and unpack it beside the PDF/text cache. Prefer
  the TeX source for theorem statements, displayed equations, notation, labels,
  and appendix references; use PDF extraction mainly for quick search and for
  confirming page context.
- If the local PDF/text cache already exists in the paper folder, use those
  local files. If an arXiv source cache exists, use it too. Do not search the
  web again, re-download the paper, or re-run extraction unless the cached
  source version is missing, corrupted, or known to be the wrong version. If a
  public filtered checkout omits the cache, recreate it locally from the
  recorded source URL and keep the generated cache out of Git.
- When `pdftotext` output is garbled for formulas, stop trying to reconstruct
  the formula from layout text. Read the cached TeX source directly and cite
  the source line/macro in the paper-facing comment or plan note when it
  changes the Lean statement.
- Read the abstract, introduction, model section, and theorem statements first;
  then search the cached text for every named `Definition`, `Lemma`,
  `Proposition`, `Theorem`, `Corollary`, and appendix result.
- Before deep proof work, build a source-block map: one row per paper-facing
  definition, displayed formula, named result, and proof-critical appendix
  claim, with source location, dependencies, intended Lean declaration, status,
  and likely library APIs. Use this map to drive the DAG, paper-facing skeleton,
  and review dashboard. Keep public theorem signatures stable once proof work
  begins; if translation is wrong, repair the statement early rather than
  letting proof search drift the target.
- Create the paper folder contract artifacts immediately: local `.gitignore`,
  `status.json`, `MainTheorems.lean`, `PaperInterface.lean`,
  `docs/DependencyDAG.tex`, and the private `FORMALIZATION_PLAN.md` scratchpad.
  Public paper folders should not track paper-local README/planning/handoff
  markdown unless the user explicitly asks for it.
- Draft paper-facing theorem signatures before building a helper tower. If the
  direct statement is too hard, create an explicit bridge theorem whose name and
  assumptions describe the remaining gap.
- Run a retrieval-grounding pass before inventing a new model or helper API:
  search Mathlib, Cslib, Optlib when present, and existing `EconCSLib/` modules
  for the source concept and proof role. Prefer existing formal concepts; if a
  paper-local encoding is necessary, add a small equivalence or sanity theorem
  before using it downstream.
- During intake, classify reusable primitives by library area. Upstream only
  seams that pass the second-paper test, such as finite PMF/Markov kernels/MDPs,
  probability inequalities, monotonicity/comparison lemmas, allocation
  primitives, or mechanism interfaces.
- Keep a live private status table or plan from the first scaffold onward. The
  public source of truth is `status.json`; each row must distinguish
  source-faithful wrappers, auxiliary analogues, conditional wrappers, and
  unstarted paper results.

### 1.3 Paper Folder Contract

Each paper-specific folder should be auditable by a human who wants to compare
the Lean statements against the paper.

- **Required Template Structure:** Every public paper folder must keep the root
  focused on Lean/status files and put human/audit artifacts in subfolders:
  1. A `status.json` file holding the paper status and dashboard metadata.
  2. A `docs/DependencyDAG.tex` proof roadmap and rendered
     `docs/DependencyDAG.pdf`.
  3. A `docs/FINAL_VALIDATION_REPORT.md` when the paper has a final validation
     claim.
  4. `audit/*.json` for tracked LLM/source-audit sidecars.
  5. A `MainTheorems.lean` file holding the paper-facing wrappers.
  6. A `PaperInterface.lean` file holding the compact human-facing definitions
     and named theorem statements.
  7. A local `.gitignore` file.
- **Local Gitignores:** Every paper folder *must* contain its own `.gitignore`
  that ignores local source PDFs and LaTeX auxiliaries such as `*.aux`, `*.log`,
  `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`, but it must not hide the rendered
  dependency DAG. If the folder uses a broad `*.pdf` ignore for source PDFs, add
  an explicit `!docs/DependencyDAG.pdf` exception. The overall repo `.gitignore` may
  contain generic LaTeX auxiliary patterns and source-cache patterns with
  explicit exceptions for project-written planning/audit/handoff/citation notes.
  Do not add a blanket paper-local `*.txt` ignore if it would hide useful
  planning documents.
- **Reproducible PDF/text/source cache:** A copy of the source PDF must be
  downloaded once and kept in the local paper folder so humans and agents can
  read exactly what is being reproduced. Immediately run
  `pdftotext Source.pdf Source.txt` or an equivalent paper-named extraction in
  the same folder and use that cached text file for named-statement searches.
  For arXiv papers, also cache and unpack the TeX source archive once; use it as
  the authoritative source for formulas when PDF extraction is ambiguous or
  garbled. These PDF, extracted-text, and source-archive caches are working
  artifacts, not public repository content by default. Keep them local/ignored
  in public checkouts unless redistribution rights have been checked.
  Project-written `.txt` planning notes, handoffs, and audit notes are private
  by default. Public paper folders should track only source-safe citation notes,
  final reports, DAG/proof artifacts, Lean files, `status.json`, and audit JSON
  sidecars unless the user explicitly asks for another progress artifact. Work
  from local caches when they exist; do not repeatedly search the web or re-run
  extraction unless the source PDF or source archive changes.
- Public filtered checkouts may omit ignored source PDFs, extracted text caches,
  and unpacked source archives. During final validation, do not claim a local
  PDF/text/source cache exists unless it is actually in the checkout; state the
  public source URL and any local ignored cache used for the audit, and treat
  repository-audit missing-source-cache warnings as public-release packaging
  notes rather than theorem gaps.
- **Private README/Plan Requirements:** If a private paper `README.md` or
  `FORMALIZATION_PLAN.md` exists, it must clearly identify the exact source
  version of the paper (for example arXiv version `vX` or conference year) and
  provide URLs. Public-facing source/version information belongs in
  `status.json` and `docs/FINAL_VALIDATION_REPORT.md`.
- **DAG Node Wording:** `DependencyDAG.tex` is a proof roadmap for humans, not
  a formalization changelog. Once a node is marked formalized, its text should
  state or briefly summarize the paper claim. Do not fill green nodes with
  implementation notes such as helper families, algebra rewrites, or "closed"
    status language; keep those details in private status/proof notes or the
    final report. Partial/conditional nodes may mention the missing proof
  obligation, but should still foreground the paper statement. During a pause
  or handoff pass, audit the DAG for this specifically: if a node reads like a
  session log, rewrite it before rendering.
  Visual DAG nodes must be paper-facing, not Lean-code-facing: do not put Lean
  declaration/function/theorem names, record names, helper identifiers,
  wildcard declaration families, or `\texttt{...}` code labels in DAG node
  text. A node should say "Theorem 1 likelihood decomposition" or "compact
  process/stopping certificate", not a Lean identifier such as
  `theorem1_...`, `Theorem2PrimitiveSourceModel`, or
  `HomogeneousPoisson...`. Put Lean names in README/status/final-report audit
  rows, not in the visual DAG.
  Compatibility routes, older sufficient endpoints, alternate proof attempts,
  and implementation-only wrappers are not DAG node content once the
  paper-facing result is represented. Record them in the README or final
  validation report if they matter for auditability.
- Add one central Lean file for paper-facing theorem statements, conventionally
  named `MainTheorems.lean`, `PaperTheorems.lean`, or the existing paper root if
  the folder already has a root module. This file should state and prove only
  the main theorem wrappers and import the detailed proof files.
- Main theorem definitions/functions in that central file should mirror the
  paper statement closely enough that a human can inspect just this file and
  verify the intended theorem was formalized. Use paper theorem numbers/names in
  docstrings and keep wrappers thin.
- If `MainTheorems.lean` is becoming a large implementation file, add narrow
  proof-route files instead of appending more proof bodies there. A route file
  should own one stable declaration cluster or named proof path and be imported
  by the central theorem file. Splitting is allowed and often desirable when it
  will reduce repeated proof-loop rebuilds, localize expensive imports, or give
  concurrent agents disjoint ownership. Avoid risky mass moves just to split a
  file; move a cluster only after its imports and targeted build are already
  stable, and keep `MainTheorems.lean` as the re-exported paper ledger.
- Any proof-facing interface or route file is an implementation bridge. Keep it
  thin and source-shaped, and keep `PaperInterface.lean` as the human review
  surface.
- Every paper folder has exactly one canonical human-review Lean surface:
  `PaperInterface.lean`. Do not introduce filename variants such as
  `HumanReview.lean`, `ReviewInterface.lean`, or paper-specific alternatives.
  If an older `PaperInterface.lean` has grown into a broad proof/API surface,
  rename that broad file to an implementation-facing name such as
  `ProofInterface.lean`, update imports, and replace `PaperInterface.lean` with
  a compact review surface.
- `PaperInterface.lean` is the file consumed by the human review dashboard. It
  should be declaration-ordered by paper section and should expose only the
  paper-facing definitions, formatted paper objects, and named theorem
  statements (with assumptions and short paper-context comments). It should not
  contain helper families, proof-seam checks, algebraic plumbing, or endpoint
  changelogs; put those in `MainTheorems.lean`, `ProofInterface.lean`, or
  `PostPaperAudit.lean`.
- Prefer source-shaped final models over proof-adapter structures in
  `PaperInterface.lean`, then audit broad paper-module exports so old adapters
  do not reappear as public endpoints.
- Keep the interface row count close to the paper's named definitions and
  results. Do not expose every theorem-route variant, support wrapper,
  diagnostic, certificate, or PMF/law specialization as its own dashboard row.
  If a proof pass makes `PaperInterface.lean` grow far beyond the source's
  named result list, trim it before refreshing the dashboard or calling the
  paper ready for review.
  As a concrete dashboard rule, more than 30 rows requires a no-paper-context
  LLM review-surface audit saved as `review_surface_llm.json`, checking whether
  every row is genuinely paper-facing and should be present. At 120 or more rows,
  the dashboard should warn even if an audit exists; treat that as a prompt to
  curate `PaperInterface.lean` or `status.json` `review_surface.include_names`
  before broad human review.
  Do not overcorrect by shrinking a substantial completed paper to only a few
  formula rows. A final review surface should cover all main source theorem
  blocks, key displayed formulas, examples, and appendix/convergence pieces
  that support the paper claim. LLM-as-judge legibility and source coverage are
  more important than a small row count: adding rows is correct when it makes a
  source-visible claim explicit enough for semantic checking. If a large paper
  naturally needs many source-facing rows, keep them and improve slices,
  source statements, and row grouping instead of hiding paper content.
  A dashboard with hundreds of rows is a warning that implementation endpoints
  may have leaked into the human interface, not a reason to delete
  source-visible content. Curate the source-facing definitions/results in the
  paper-local `status.json` `review_surface`, and move broad proof aliases to
  `ProofInterface.lean`; use slices to keep a large but legitimate review
  surface navigable.
  Final reports should cite the post-filter human-review row count and describe
  how the source inventory is covered. If the count is still in the hundreds,
  audit whether rows are source-facing; keep them when they are needed for
  complete source coverage.
- Before asking for dashboard review, run a statement-surface audit: every
  dashboard row should be a paper-facing definition, formula, or named source
  statement; the total should be close to the paper's named result inventory.
  If there are more than 30 rows, perform the independent LLM surface audit and
  save the verdict, row count, and dashboard digest in `review_surface_llm.json`.
  Include validator provenance in that sidecar: `validator`, `validator_type`,
  `validated_at`, and `comment`, using the same conventions as
  `statement_match_llm.json`.
  If there are many extra rows or the LLM says `needs_curation`, first trim
  `PaperInterface.lean`, then narrow `status.json` `review_surface.include_names`;
  do not use slices to legitimize a bloated human review file.
- Do not confuse row-local validation with paper-level coverage. A clean
  `statement_match_llm.json` only says that existing dashboard rows match their
  supplied source statements; it does not say that every paper statement is
  represented. Maintain an explicit `paper_statement_map.json` inventory of the
  source paper's definitions, displayed/source-defining formulas, theorem
  blocks, named subclaims, and appendix results that are intended formalization
  targets. Then populate `paper_coverage_llm.json` with an independent
  source-to-row judgment: each inventory item should be `covered` by one or more
  dashboard row names, `conditional_boundary` when the row-level statement judge
  records an explicit boundary assumption, `covered_by_support` when a named
  source proof-route lemma is formalized in support declarations but omitted
  from the compact dashboard, `partially_covered`, `missing`, or explicitly
  `out_of_scope`/`not_a_paper_target` with a reason. Run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --paper-coverage-precheck`.
  Compactness is not a valid reason to mark source-visible review targets out
  of scope. Main-text definitions, examples, remarks, propositions,
  theorems/corollaries, and main-text lemmas should have review-legible
  dashboard rows with row-local statement judgments. Appendix
  theorems/corollaries should also be covered. Appendix lemmas are a judgment
  call, but if they carry paper-facing mathematical content needed for the
  formalized claim, expose individual or tightly grouped rows instead of one
  broad "wrapped support" placeholder.
  For public-facing statuses (`formalized` or `partially formalized`), the
  audit requires an explicit source inventory; heuristic source-text extraction
  is only a seeding aid and must not satisfy closeout by itself.
  The inventory must be resolvable in the repo where the audit runs: if raw
  source text/PDF cannot be tracked publicly, put a compact source statement or
  paraphrase plus citation/location directly in `paper_statement_map.json`
  rather than pointing to a private `source.txt`.
  If you create the map with
  `scripts/seed_paper_statement_map_from_dashboard.py`, mark it as
  `source_inventory_kind: "dashboard_seeded_preliminary"` and
  `source_curated: false`. That map is useful for making the coverage machinery
  concrete, but it is not evidence that the paper source has been exhaustively
  inventoried. A very large count can mean the dashboard contains many
  formula/proof-support rows, not that the paper has that many named source
  statements; for example, an 80+ row source inventory should trigger a source
  curation pass that separates named paper statements from subformula/support
  rows.
  Before preparing a public PR, replace any dashboard-seeded preliminary map
  with a curated source inventory whenever the row count is inflated by
  alternative theorem routes, kernel/probability support lemmas, or
  implementation sanity checks. Keep explicit boundary assumptions in
  `review_surface.assumption_names` and `assumption_match_llm.json`; do not
  count those rows as ordinary source statements in `paper_statement_map.json`
  unless the paper itself states them as theorem targets.
  After changing the review surface or assumption-source metadata, refresh the
  paper dashboard cache, regenerate `paper_coverage_llm.json`, rerun the
  assumption-provenance audit, and refresh `source_record_audit.json` plus
  `source_record_match_llm.json` whenever the audit digest or prompt version is
  stale.
- Treat source-to-Lean coverage as a chained audit, not two unrelated green
  checks. A source item marked `covered` in `paper_coverage_llm.json` must link
  to concrete `review_rows`, and those rows must have current row-local LLM
  correctness judgments in `statement_match_llm.json`, even when the row is an
  assumption row. The statement-match judgment must be for the exact current
  dashboard paper statement of the linked row; the script checks the saved
  paper-statement digest automatically, so a green judgment for an old or
  different statement does not count. `assumption_match_llm.json` is a separate
  provenance/boundary lane for whether an assumption is source-derived or a
  partial formalization boundary. Run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --source-to-lean-precheck`
  before claiming a paper is complete; use `--source-to-lean-check` as the
  blocking version once any intentional support-only legacy rows have been
  promoted or reclassified. A theorem/lemma/proposition/corollary source item
  covered only by `support_declarations` is a warning sign: promote it to a
  source-facing `PaperInterface.lean` row with Lean-to-TeX and statement-match
  judgments, or mark the paper status/coverage boundary honestly.
  The repository audit treats required source-visible targets marked
  `out_of_scope`/`not_a_paper_target` as failures. If the dashboard grows, make
  it more navigable with slices and clear source-facing statements rather than
  shrinking away paper content.
- Treat paper coverage as three separate LLM-as-judge lanes:
  1. **Source inventory lane.** Read the source PDF/TeX/text (or a previously
     recorded source inventory with source locations) and write
     `paper_statement_map.json` from paper statements, not from Lean names.
     Mark source-derived inventories as `source_inventory_kind:
     "source_curated"` and `source_curated: true`. Include source evidence such
     as theorem/equation number, section, source-cache line, or a compact quote
     or paraphrase. If an item is intentionally out of scope, record that
     explicitly rather than omitting it silently.
  2. **Source-to-dashboard lane.** A separate judge reads each source inventory
     item and the candidate human-dashboard rows, then records in
     `paper_coverage_llm.json` whether the source item is `covered`,
     `conditional_boundary`, `covered_by_support`, `partially_covered`,
     `missing`, or `out_of_scope`. The sidecar must use `audit_kind:
     "source_to_dashboard_llm"` (or `"source_to_dashboard_agent"`),
     `source_grounded: true`, linked `review_rows` for dashboard coverage,
     `support_declarations` for support-only coverage, `source_evidence`, and a
     nontrivial match reason. Exact name/alias matches from
     `scripts/seed_paper_coverage.py` are only `audit_kind:
     "exact_key_scaffold"` and must not pass a closeout audit.
  3. **Row-local statement lane.** Generate `lean_to_tex_llm.json` from Lean
     statements alone, then have another judge compare that translation against
     the dashboard row's paper statement text in `statement_match_llm.json`.
     Every row-local judgment must save Lean, TeX, and paper-statement digests;
     the source-to-Lean audit uses those digests to ensure the judge checked
     the same statement that the linked row currently claims to cover. This
     answers whether a dashboard row says what its displayed paper statement
     says; it does not answer whether all source statements are represented.
  4. **Joined source-to-Lean lane.** The dashboard script joins
     `paper_coverage_llm.json` to the row-local correctness files and emits
     `row_statement_match_links`/`row_correctness_*` JSON records with source
     digests, row digests, row names, validators, timestamps, and stale flags.
     Inspect these records when debugging a false completion: the paper is not
     actually source-to-Lean clean unless every covered source statement either
     has passing linked row correctness judgments for the same current row
     statements, or is explicitly and honestly marked as conditional/out of
     scope/support-only.
- Paper-facing definitions in `PaperInterface.lean` must show their actual
  Lean definition bodies, not only their function types or an opaque imported
  library name. If a dashboard row for a definition renders as only
  `A -> B -> ...` or `ℝ -> ...`, stop and fix the interface/dashboard before
  asking a human to review it. A reviewer should be able to compare the paper's
  displayed formula directly against the Lean formula in that row.
  When the reusable implementation must remain an imported definition or short
  alias, add a source-equation wrapper theorem in `PaperInterface.lean` such as
  `_formula`, `_iff`, `_fields`, `_rule`, `_content`, or `_matches`, and include
  that wrapper in `status.json` `review_surface.include_names` instead of the
  opaque alias. The wrapper must make the formula visible, but visibility is
  not proof provenance: it is closed only when the formula is derived in Lean
  from source model primitives or from separately validated paper assumptions.
  If the wrapper asserts a displayed equation, inequality, iff, definition, or
  source-defining formula as a theorem premise, certificate field, or source
  row, the downstream endpoint is partial until that premise is derived or
  routed through `Assumptions.lean` and approved by the source-assumption judge.
  The repository audit checks this failure mode when an included alias has an
  available source-equation wrapper.
  The dashboard/audit parser treats `paper_...` declarations in
  `PaperInterface.lean` as review rows even if their docstrings are removed or
  converted to ordinary comments. Do not keep auxiliary `paper_...` aliases in
  `PaperInterface.lean` merely to support downstream proof code. Move or omit
  them, and expose only the source-shaped wrapper row, such as a finite-vector
  objective wrapper or an explicit `_fields` wrapper, in the review surface.
  Every displayed or source-defining formula used by a paper-facing result
  should have an exact formula/subclaim row. Do not collapse several displayed
  formulas or subclaims into a broad numbered-result row such as a metric
  package, source surface, or model summary when claiming full validation.
  The independent judge must be able to compare the full theorem scope, not just
  the label or endpoint shape: signs, constants, domains, all quantifiers,
  inequality direction, normalizing factors, hypotheses, subparts, conclusions,
  and iff/implication direction for each formula-bearing row. A `matches` verdict
  is allowed only when the row is equivalent to the full source statement, or to
  a source subpart explicitly identified as such. If a Lean row omits a source
  subpart, adds a non-source condition, weakens/strengthens the conclusion, hides
  a displayed formula in a source-row package, or represents several displayed
  formulas with one broad aggregate, the judge must return `mismatch` or
  `uncertain`.
  When an LLM-as-judge row is `uncertain`, inspect the actual Lean statement
  before accepting the uncertainty. If the Lean row is only a function
  signature, imported alias, structure name, or conclusion predicate, fix
  `PaperInterface.lean` by exposing the equation, fields, iff, or theorem
  conclusion. If the Lean row is already source-shaped but the TeX draft erased
  binder context such as `W` versus `W'`, regenerate the Lean-to-TeX draft and
  then rerun the judge; do not change a correct Lean statement to satisfy a bad
  draft.
  Treat source-equation-wrapper findings from `scripts/audit_repository.py` as
  review-surface blockers: if an included alias has a paper-facing `_formula`,
  `_iff`, `_fields`, `_rule`, `_content`, or `_matches` wrapper available, the
  dashboard row should expose that wrapper, not the opaque alias.
  Treat stale Lean-to-TeX or statement-judge sidecars the same way: stale
  sidecars do not change a Lean proof, but they invalidate the current
  source-match claim until regenerated and rechecked. After renaming aliases,
  splitting aggregate rows, or changing source-provenance docstrings, refresh
  the uncached dashboard cache, regenerate tracked sidecars from that current
  cache/surface, remove obsolete keys, and run the paper's statement precheck
  before carrying the result into a report, generated status table, or public PR.
  Broad aggregate rows are not acceptable substitutes for formula-level review.
  If one Lean declaration summarizes several paper formulas or subclaims, expose
  separate paper-facing rows for the exact formulas/subclaims and include those
  rows in `status.json`; keep the aggregate theorem in the audit ledger only if
  it is useful for proof coverage.
- Every dashboard row should label source provenance in the `PaperInterface.lean`
  docstring. Use dashboard-only lines such as `Source status: direct paper
  statement`, `Source status: direct paper formula`, `Source status: corrected
  source statement`, or `Source status: added audit row`; for any corrected,
  edited, weakened, strengthened, or added row, include a `Source note: ...`
  line that states exactly how it differs from the paper. The dashboard strips
  those lines from the statement text and displays them as badges/notes. Treat a
  missing source-deviation note as a review-surface bug, not as a harmless
  documentation omission.
- Every non-derived paper-facing theorem premise should appear as a named
  assumption declaration in paper-local `Assumptions.lean`, imported by
  `PaperInterface.lean` when a theorem signature references it. Add the
  declaration to `status.json` `review_surface.assumption_names` and run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --assumption-precheck`
  at review boundaries. If the assumption judge is missing, stale, uncertain,
  or says `not_paper_assumption`, the downstream theorem is conditional/partial
  until that premise is derived or the source assumption is documented. Do not
  hide proof certificates, source-row equations, threshold identities, or
  normalizer formulas inside theorem parameters to avoid this workflow; those
  are either Lean proof obligations to close or explicit paper assumptions to
  validate.
  `scripts/audit_repository.py` expands review-surface declarations, checks
  direct paper-local `abbrev`/`def` aliases, scans paper-facing declarations
  outside `PaperInterface.lean`, and runs Lean-native `#print axioms` on
  paper-facing rows. Moving a certificate to `ProofInterface.lean` does not
  make a completed theorem closed if the expanded paper-facing statement still
  exposes that certificate. The dashboard `--assumption-precheck` path also
  invokes these premise and axiom checks for the selected paper, so it may
  report unresolved proof premises even when the explicit assumption table has
  zero rows. If that audit flags an alias target, first refresh the dashboard
  cache and inspect whether the premise is an ordinary scalar condition already
  visible in the expanded statement or a true certificate/source-boundary
  package. Scalar paper conditions belong in the statement and
  statement-validation lane; certificate/source-boundary packages must be
  discharged, exposed as validated paper assumptions, or downgraded to
  conditional/partial.
  The checker must inspect anonymous top-level arrows in expanded declarations
  as well as named binders. A premise whose type head is a certificate, row
  package, regularity bundle, capacity/cutoff formula package, or source
  boundary is still a visible proof obligation even if Lean prints it without a
  name. Conversely, avoid false positives from ordinary source equations that
  mention a constant with a certificate-like name inside the formula; classify
  the premise type head, then use exact premise comments in `Assumptions.lean`
  to show how the assumption judge reviewed it. Use Lean's axiom printer, not a
  custom recursive text scan, for transitive proof dependencies.
  At closeout/public-promotion boundaries run the combined recursive
  provenance audit:
  `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`.
  Use `--include-active` when the paper being closed is in the active-paper
  allowlist; otherwise it may be omitted. Treat the generated Markdown as the
  durable closeout ledger for Lean axiom closure, broad/opaque paper-facing
  rows, source-row formula boundaries, visible premises, and source-shaped
  reusable-library APIs. A paper can be marked `formalized` only
  if this report has no theorem-status findings for that paper, except findings
  already resolved by deriving the premise from primitives or by routing it
  through a source-validated `Assumptions.lean` declaration. If a visible
  premise finding remains, the paper/result is partial or conditional and the
  same boundary must appear in `status.json`, the DAG, and the final validation
  report.
  Also run
  `python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`
  after reusable library edits; that pass reports direct certificate/source
  boundary APIs and rejects source-shaped reusable definitions. Use it together
  with the paper-interface axiom audit, not as a replacement for Lean's own
  transitive dependency check.
- Keep proof-linkage declarations such as `paper_definition_eq_library_name`,
  bare aliases for generic predicates, and other implementation checks out of
  `PaperInterface.lean`. Put them in `ProofInterface.lean` or another
  proof-facing file so the dashboard asks humans to review only source-facing
  definitions and named results.
- For new papers, create `PaperInterface.lean` during intake from the scaffold,
  not only after the proof is complete. Keep it synchronized with the proof plan
  and DAG so the eventual human review file grows with the formalization.
- When scaffolding a paper (for example through `scripts/new_paper.py`), run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --refresh-cache`
  once so the dashboard snapshot is generated before the first review workflow.
- Do not refresh or precheck the review dashboard after every small
  declaration-level edit. During active proof work, keep moving with Lean
  builds and source-facing docs; refresh the dashboard at natural review
  boundaries instead: after a coherent batch of `PaperInterface.lean`
  statement changes, before a human review session, before final handoff, or
  before declaring a paper/proof phase complete.
- If you only added or adjusted a few paper-facing declarations and are leaving
  a short interim stopping point, it is enough to record the changed
  declaration names in the README/plan/handoff and defer dashboard refresh to
  the next review boundary.
- The launcher checks freshness against the logged trace on startup; if an old
  check is out of date, it warns you and you can immediately re-save checks.
  If interface docstrings or source-facing statement text changed, expect old
  human review rows to become stale. Do not edit or rewrite the review log to
  clear that state; leave the dashboard warning and tell the reviewer which
  rows need to be resaved.
- Reserve the dashboard word "reviewed" for actual human review-log entries.
  The dashboard counter means "a validation row was saved"; if an agent writes
  entries, the UI will still increment the counter, but that is not human
  review. Do not populate `.review_traces/paper_theorem_validations.jsonl` with
  agent-generated entries just to clear `0/N reviewed` or `need attention`.
  For agent validation, write a tracked source-audit artifact such as
  `SOURCE_AUDIT.md`, label it clearly as an agent audit, and report the
  dashboard human-review state separately.
- Human review logs are intentionally commit-eligible: `.gitignore` should keep
  `.review_traces` caches/logs local while unignoring
  `.review_traces/paper_theorem_validations.jsonl`. After an actual human
  review pass, inspect and commit the paper-local JSONL log if those judgments
  should become part of repository history; do not commit generated dashboard
  HTML, cache JSON, rendered statement images, or `review-dashboard.log`.
- The human review-log `user` field should default to the authenticated GitHub
  username, while remaining editable in the browser. Preserve the default order:
  explicit `--user`, GitHub environment variables, authenticated `gh` username,
  git config, then OS username.
- It also shows compact paper-source action links (open PDF/text file), so the
  reviewer can quickly jump back to source wording when needed.
- Paper-facing formulas that look like LaTeX are rendered in the dashboard so
  theorem statements are easier to read without full Lean familiarity.
- Near the beginning of a new paper, run the smaller statement target-setting
  pass before serious proof work. After the source inventory and first compact
  `PaperInterface.lean` skeleton exist, generate `lean_to_tex_llm.json` from
  Lean statements alone, generate `statement_match_llm.json` from only the
  source statement plus that translation, then run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --statement-precheck`.
  Use `--statement-check` instead when a nonzero exit is useful for automation.
  Then run `python3 scripts/review_dashboard.py --paper <paper-folder>
  --assumption-precheck` before treating the matched statements as certified
  targets. The statement judge is row-local and will not catch a source-domain
  premise that was split out of a definition into theorem hypotheses unless the
  expanded dashboard cache has been refreshed and the premise is visible in that
  statement.
  If `--statement-check` fails here, treat it as target-setting feedback: fix
  `PaperInterface.lean` or the extracted source statement before building long
  proofs around that row. If `--assumption-precheck` reports hidden premises,
  derive them, move true paper assumptions to `Assumptions.lean`, or mark the
  endpoint partial/conditional before calling the target ready.
  Use automated semantic-alignment checks as triage, not certification. A high
  match score or `matches` judgment is evidence that a human should inspect the
  row less urgently; it is not proof that the theorem is source-faithful. A low,
  stale, or inconsistent alignment result should block deep proof work on that
  row until the source statement, Lean declaration, or visible assumptions are
  repaired. Give special attention to quantifier order, implication direction,
  constants/factors, domains/support assumptions, equivalence-vs-one-way
  statements, asymptotic notation, and hypotheses moved from definitions into
  theorem parameters.
  This early pass deliberately skips workflow scaffolding: do not update the
  DAG, final validation report, human-review log, or review-surface audit just
  because the target-setting pass ran. Its purpose is to catch wrong theorem
  targets before proofs are built around them.
- For both the early target-setting pass and the full review-boundary pass, make
  sure each dashboard row has one concrete source statement. If automatic
  TeX/text extraction is missing, over-broad, or includes surrounding
  exposition, repair the paper-facing statement text before running the judge.
  Put declaration-keyed source statements in a source-inventory/report section,
  not in generated audit output. `Statement Translation Audit` is downstream
  evidence and must never become the source text for a later judge pass.
  Report parsers should treat all Markdown heading levels (`##` through
  `######`) as section boundaries and ignore generated audit sections such as
  `Statement Translation Audit`; if source statements start looking like
  validator rows, stale flags, or `uncertain` comments, fix the parser or final
  report section order before regenerating LLM sidecars.
  If nearly every row is `uncertain`, assume a parser/source-statement mapping
  failure until proven otherwise: fix the source extraction or record a
  paper-wide source-map issue, instead of leaving every row individually
  uncertain as if each theorem were separately ambiguous. When a parser failure
  is the real problem, the dashboard/report should expose one paper-wide parser
  or source-map status rather than a table that makes every theorem look
  independently uncertain.
  A judge result of `uncertain` means the statement target is not certified yet;
  do not rewrite it as "formalized with caveat" or "partial formalization"
  unless the mathematical formalization itself has that status.
  In generated public tables, keep `LLM-as-judge statement translation` as a
  translation/equivalence status column, not an assumption-provenance column.
  Raw judge rows with `resolution: conditional_boundary` should render as
  paper-facing `formalization-boundary statement rows`; do not label them
  "additional assumptions" unless they are genuine non-paper hypotheses in the
  separate assumptions section.
  If the same public table also shows a human-review denominator, the LLM row
  summary must reconcile with that denominator: report statement-translation
  rows and explicit source-condition/assumption rows as separate components
  instead of showing an unexplained smaller statement-only total.
- Use the dashboard's normalized `statement_digest` values for sidecar digests,
  not raw SHA-256 of unnormalized strings. Lean-statement sidecar hashes must
  be source-stable: hash the source declaration text exposed by the review
  surface (`interface_source` / raw paper-facing declaration), not optional
  rendered `#check` preview text. The preview is useful for humans, but it can
  differ between a warm local checkout and a cold CI checkout if Lean preview
  subprocesses time out or fall back to raw signatures. New tracked
  `lean_to_tex_llm.json` entries should include `lean_statement_sha256`; new
  `statement_match_llm.json` entries should include Lean, paper, and TeX
  statement digests so stale target checks work.
- At a statement-review boundary, run the exact statement-translation workflow:
  1. Curate `PaperInterface.lean` first. It should contain paper-facing
     definitions, formulas, examples, remarks, and named source results that a
     reviewer or LLM-as-judge should inspect. Do not include proof plumbing,
     empirical sections, helper lemmas, or library-internal facts unless they
     are explicitly paper-facing. Completeness beats compactness: do not hide
     named source content only because it makes the review surface longer.
  2. If the dashboard has more than 30 rows, run a no-paper-context surface
     pass over the row list and save `review_surface_llm.json`. The pass asks
     only whether each row belongs on the human-facing paper surface. At 120 or
     more rows, treat the surface as a warning even if an audit exists; improve
     slices, source statements, and row grouping, but do not remove
     source-visible content that the coverage audit needs. More rows are fine
     when they make the review surface more legible to the LLM-as-judge and the
     source inventory confirms that they cover paper claims.
  3. Build or refresh `paper_statement_map.json` from the source paper itself,
     not from the Lean row list. It should be a canonical source inventory with
     aliases only as lookup aids. Then generate `paper_coverage_llm.json` with
     a separate paper-level judge that asks whether each source inventory item
     is represented by one or more current dashboard rows. This is the only
     LLM-as-judge lane that answers "did we include every paper statement?";
     the row-local statement judge below cannot answer that question.
     A dashboard-seeded map is only a temporary scaffold; before citing it as
     paper coverage, compare it against the source PDF/TeX and either add
     missing named statements, mark support-only proof-route lemmas as
     `covered_by_support` with explicit `support_declarations`, mark rows that
     match only under a declared proof boundary as `conditional_boundary`, or
     mark genuinely non-target source material as `out_of_scope` with reasons.
     Do not use `out_of_scope` for source-visible named material merely because
     adding rows would make the dashboard longer.
  4. Generate `lean_to_tex_llm.json` from the Lean statements alone, with no
     paper text and no proof context. Use one item per current dashboard row.
     The translator prompt must be literal rather than explanatory: preserve
     every visible binder, variable, hypothesis, domain restriction, premise,
     equivalence/implication direction, and conclusion in mathematical form. It
     must not compress the statement into a theorem label, omit conditions, or
     turn a conditional theorem into an unconditional prose summary. For new
     tracked sidecars, use object entries:
     `{ "tex_statement": "...", "lean_statement_sha256": "..." }`. Legacy plain
     string entries are accepted, but object entries make stale-draft checks
     possible.
  5. Generate `statement_match_llm.json` with a separate judge that sees only
     the original paper statement and the Lean-to-TeX draft, not the Lean proof
     or surrounding paper. The paper statement supplied to the judge must be the
     complete source theorem/definition/formula text or an explicitly named
     source subpart, including all preconditions and subclaims needed to decide
     equivalence. Do not feed the judge a theorem title, generated report
     summary, or selected excerpt as the paper side. Each entry should include
     `judgment`, `reason`,
     `lean_statement_sha256`, `paper_statement_sha256`, and
     `tex_statement_sha256`. Valid judgments are `matches`, `uncertain`, and
     `mismatch`. The sidecar should also record validator provenance: put the
     model or agent name in `validator` (for example `gpt-5-codex`), set
     `validator_type` to `model` or `agent`, record `validated_at`, and use
     `comment` for any validator-facing note that should appear in the status
     export. Top-level validator/comment fields are defaults; item entries can
     override them when a different model or agent checked a specific row.
     Keep the raw `judgment` strict. If a paper row is a known, user-approved
     conditional result because it depends on an external/library theorem,
     analytic theorem, solver, runtime model, or other explicit proof boundary,
     do not mark it `matches`. Mark the raw row `mismatch` and add
     `resolution: "conditional_boundary"`, plus `boundary_type`,
     `boundary_names`, `conditional_premises` when applicable, and
     `resolution_reason`. This records an intentional mismatch/known external
     dependency without hiding the source-statement gap. Any visible extra
     theorem premise accepted this way must appear in `conditional_premises`;
     otherwise the hidden-premise audit should keep reporting it as unresolved.
     The judge prompt must be exact-formula and full-theorem aware: it should
     reject broad aggregate rows when the paper has displayed equations,
     inequalities, iff statements, definitions, or source-defining formulas that
     are not exposed as their own row or subclaim. Ask it to compare every
     hypothesis, source assumption, domain, quantifier, subpart, conclusion,
     sign, constant, normalizing factor, inequality direction, and iff/
     implication direction. The judge pass is recursive for formula-bearing
     terms: if the Lean row refers to a paper-local or reusable-library
     definition that encodes a displayed source formula, provide the expanded
     formula or a proved paper-local equivalence as part of the Lean-side
     material to be judged. It must mark `mismatch` or `uncertain` if the Lean
     draft is conditional when the paper statement is unconditional, omits a
     paper conclusion, changes a theorem from equivalence to one direction, uses
     a source-row/certificate package instead of the displayed formula, hides a
     source formula inside a generic library definition, or proves only a
     helper/endpoint that is not the full paper statement.
     Also scan the source proof, not just the theorem heading, for stochastic
     qualifiers such as "with probability 1", "almost surely", "with high
     probability", "probability tends to 1", or "probability zero". If the proof
     closes the named result only through such a probabilistic event statement,
     include that qualifier in `paper_statement_map.json` and judge any
     deterministic Lean wrapper as conditional unless Lean also models the
     probability space/event and proves the qualifier.
     For rows that mention records/certificates/source models, first generate
     or refresh `source_record_audit.json` with the skill helper. Feed the
     relevant row and field entries, including Lean `#check` output, to the
     judge. The judge must verify that each mathematical source statement in
     those fields is proved from primitive Lean declarations, explicitly
     validated as a paper source assumption, or intentionally marked as an
     external boundary. A field projection is evidence that the statement was
     assumed in the record, not evidence that it was proved.
     Source-record audit payloads must be reproducible across machines. Store
     source files as repo-relative paths, never as `/home/...` absolute paths,
     because those paths enter the audit prompt/digest surface and can make a
     fresh CI checkout report stale `source_record_audit_sha256` values even
     when the Lean statements are unchanged. After touching the source-record
     helper, source maps, `PaperInterface.lean`, or source-record-bearing
     theorem signatures, regenerate both the code-backed
     `source_record_audit.json` payload and the matching
     `source_record_match_llm.json` sidecar for the affected rows before using
     them as evidence. The helper must distinguish source assumptions declared
     in `Assumptions.lean` from ordinary paper-interface rows; otherwise an
     assumption can be falsely judged as a theorem translation. During active
     proof work, run targeted script/unit checks and regenerate only the
     affected audit payloads needed for the changed rows. Run the full
     repository audit only at closeout/public-promotion time or when the user
     explicitly asks for post-validation.
     When prompt versions, digest fields, or cache schemas change, verify the
     audit path in both uncached and cached modes. Cached review rows must
     rehydrate all Lean, paper, TeX, source-record, and premise digests used by
     `--source-to-lean-check`; a green uncached check with a cached digest
     failure usually means the cache loader or schema migration is stale, not
     that the paper proof changed. Patch the audit script, bump the cache schema
     if needed, run `python3 -m py_compile` on changed scripts, and rerun the
     paper-local checks.
  5. Treat `mismatch` or `uncertain` as a problem with the formalized statement
     unless the translation is plainly wrong. Usually the fix is to make the
     `PaperInterface.lean` declaration more paper-facing and self-contained,
     then rerun both LLM passes.
     When refreshing stale sidecars after editing `PaperInterface.lean`, do not
     try to clear CI by lengthening preview timeouts, relying on ignored
     dashboard caches, or copying hashes from a warm checkout. Regenerate the
     tracked sidecars from the current uncached review surface and store the
     source-stable Lean declaration digest. During closeout, run a cache-free
     paper-local summary or `--statement-check`, followed by
     `scripts/audit_repository.py` or CI. If local dashboard checks pass but CI
     reports every row stale for a
     paper, suspect environment-dependent preview hashing first; fix the digest
     source rather than fighting the build cache.
     If stale rows appear after a public/private copy or a CI checkout while
     the Lean code is unchanged, first refresh the uncached dashboard surface
     and tracked LLM sidecars from that checkout. Do not copy ignored dashboard
     caches from another machine or assume stale sidecars are human-review
     failures; human review can be unreviewed, but only generated model/agent
     sidecars become stale.
     If only prompt/audit code changed and the Lean/source statements are
     unchanged, refresh the digest metadata from the current checkout and keep
     the validator judgments verbatim only after confirming the normalized
     source statement, Lean declaration text, and boundary metadata are
     identical. Never rewrite a `mismatch` or `uncertain` to `matches` merely
     because a digest or prompt version changed.
  6. Record statement-translation results in the final report's validator
     surfaces, not in an ad-hoc extra report heading. Summarize row counts,
     match/uncertain/mismatch counts, stale status, and surface-audit status in
     sections 1 and 11 as needed, then fill section 15
     `Paper-Facing Statement Validator Ledger` from the validators export. This
     is agent audit evidence, not human review.
  7. Run `python3 scripts/review_dashboard.py --paper <paper-folder> --precheck`
     before handoff. The precheck should report no stale LLM sidecars. Remaining
     `uncertain`, unresolved `mismatch`, and `mismatch` rows with
     `resolution: "conditional_boundary"` must be explicitly listed in the
     final validation report. A conditional-boundary mismatch may be accepted
     only if the same boundary is named in `status.json`, the DAG/report caveat,
     and the assumption/proof-boundary metadata.
- At a post-paper closeout boundary, run LLM-as-judge freshness and provenance
  checks before committing or pushing. A user request such as "post paper
  workflow", "audits", "finish the paper", or "commit and push after closeout"
  is sufficient trigger for the target paper's machine prechecks, but it is not
  a request to rerun LLM judges for every paper in the repository. The Python
  precheck/audit code should verify that tracked sidecars are present, current,
  non-stale, and non-flagged. Regenerate LLM sidecars only for the target paper
  rows/records that are missing, stale, structurally changed, or explicitly
  requested. Do not launch all-paper LLM-as-judge refreshes unless the user
  specifically asks for an all-paper judge refresh. This is not an in-progress
  proof check: if the paper is still known to be unfinished or waiting on
  library work, skip the closeout pass unless the user explicitly asks for it,
  and report targeted build/status results instead. The target-paper closeout
  pass must:
  - refresh the uncached dashboard row surface for the paper;
  - ensure every `PaperInterface.lean` declaration is classified: reviewed rows
    in `review_surface.include_names`, paper assumptions in
    `assumption_names`, and all proof-facing helper declarations in
    `auxiliary_names`; auxiliary slice buckets may be added solely to satisfy
    audit/readiness row-count checks, but they do not make those helpers part of
    the visible human dashboard;
  - run the no-paper-context review-surface judge for the target paper only
    when the row count exceeds the surface threshold and
    `review_surface_llm.json` is missing/stale/flagged, or when explicitly
    requested;
  - refresh the explicit source statement inventory in `paper_statement_map.json`
    when the target paper source inventory changed, then use the precheck to
    verify `paper_coverage_llm.json` against current dashboard row names. For a
    public-facing status, a missing explicit inventory is a closeout blocker
    even if the dashboard has few rows or all existing rows have clean statement
    judgments;
  - verify `lean_to_tex_llm.json` for every current non-assumption review row
    using source-stable declaration digests, and regenerate only missing/stale
    target-paper translations;
  - generate the code-backed recursive source-record audit for every row whose
    statement or visible premises mention a record/certificate/process/source model,
    and save it as `source_record_audit.json` or a dated equivalent;
  - keep the recursive audit conservative but precise: if it reports a missing
    source-shaped type solely because a primitive enum/base carrier name ends in
    a trigger suffix such as `Model`, add that name to the audit helper's
    non-source-record whitelist instead of adding a fake source judgment;
    similarly, do not classify ordinary source predicates as provenance
    packages merely because their names end in `Bound` or `Bounds` (for example
    `MarginalBound`); those belong to row-local statement matching unless they
    are inside a certificate/source-record/process/replay/bridge structure;
  - verify `statement_match_llm.json` with the strict full-statement,
    exact-formula, recursive-definition prompt metadata described above,
    including the source-record audit entries for rows that depend on such
    structures; rerun only missing/stale/flagged target-paper rows unless the
    user asks for a broader refresh;
  - inspect source-record classifications before setting the status: any
    remaining `approved_external_boundary`, `unresolved_assumed_math`, stale
    source-record digest, or missing source-record judgment makes the affected
    row partial/conditional unless a Lean constructor has discharged it or the
    status claim explicitly excludes that source item;
  - verify `assumption_match_llm.json` for every name in
    `review_surface.assumption_names`, including both source assumptions and
    any user-approved proof-boundary axiom names from `proof_boundary_names`;
    regenerate only missing/stale/flagged target-paper assumption judgments;
  - classify proof-boundary axioms as `partial_boundary`, not as source
    assumptions, and give item-level `premise_judgments` for each exact
    `-- audit-premise` line in `Assumptions.lean`;
  - treat `resolution: "conditional_boundary"` in `statement_match_llm.json` as
    a provenance suppression only for the same current review row, only with the
    current prompt version plus validator/timestamp metadata, and only for
    non-completed statuses. A `formalized` paper must still discharge or
    source-record-validate every certificate/source-model/replay/process
    premise rather than relying on a conditional row mismatch;
  - update `DependencyDAG.tex`, render and visually inspect
    `DependencyDAG.pdf`, and record that DAG audit evidence in both
    `FINAL_VALIDATION_REPORT.md` and `POST_FORMALIZATION_AUDIT.md`;
  - write `AGENT_SOURCE_AUDIT.md` as an independent source-first holistic
    audit, not as a generated summary of existing sidecars. Read the source
    paper/PDF/text first, build or verify the source inventory from the source
    itself, then inspect `PaperInterface.lean` and the Lean statements for
    omissions, hidden strengthening/weakening, and semantic mismatches. This is
    a deep agentic paper-to-Lean audit: do not start from the rows already in
    the dashboard, and do not treat the row-local LLM sidecars as the audit.
    Use `paper_coverage_llm.json`, `statement_match_llm.json`,
    `assumption_match_llm.json`, and `source_record_match_llm.json` only as
    supporting evidence after the independent pass. The note must say
    `## Overall status: PASS` only if the agent's own holistic analysis agrees
    that the source claims are covered and the Lean statements match; it must
    explicitly state that it is an "independent source-first" audit and does
    "not merely summarize existing sidecars";
  - run `python3 scripts/audit_repository.py --paper <paper-folder> --paper-closeout --include-active --info-limit 0`
    after the DAG/report updates. This targeted repository audit includes the
    DAG/final-report closeout gate; do not claim post-formalization completion
    while it reports a paper-specific missing/stale DAG or validation-report
    finding;
  - rerun the target-paper precheck and record all remaining unresolved `mismatch`,
    `mismatch` with `resolution: "conditional_boundary"`, `uncertain`, stale,
    missing, or broad-surface findings in the final report.
  After editing `status.json`, review-surface row lists, sidecar hashes, or the
  final report, rerun `source_record_audit.py` for the target paper and use the
  source-record precheck to decide whether `source_record_match_llm.json` is
  stale. Resync or rerun only stale/missing/flagged target-paper source-record
  judgments. Then rerun `review_dashboard.py --paper <paper-folder> --precheck`
  and update `review_status_export.json`/status summary fields from that final
  target-paper pass.
  Do not mark these sidecars as `matches` merely to clear a dashboard. If the
  Lean row is conditional while the paper row is unconditional, if a formula is
  hidden behind a source-model/certificate/library definition, or if the paper
  statement supplied to the judge is only a title or partial excerpt, record
  `mismatch` or `uncertain` and either fix the paper interface or carry the
  explicit conditional status into `status.json`, the DAG, and the final
  report. For an approved conditional row, use `resolution:
  "conditional_boundary"` instead of changing the raw `mismatch` judgment.
  The assumption precheck may count those named `conditional_premises` as
  accepted conditional-premise findings; do not treat unlisted hidden premises
  as covered by the boundary.
- Command recipe: use `--statement-precheck` or `--statement-check` for the
  beginning-of-paper target-setting pass; use `--precheck` or `--check` for the
  full review-boundary pass. The statement-only commands intentionally ignore
  human-review counters and review-surface row-count warnings.
- Do not treat sidecar freshness as a dashboard-only convention. For completed
  papers, `python3 scripts/audit_repository.py` should also fail when
  statement-translation or review-surface sidecars are stale, missing,
  uncertain, mismatched, or otherwise flagged. Run the paper-local dashboard
  checks for diagnosis, then run the repository audit or CI before marking the
  paper closed.
- Assumption provenance checks can invoke Lean hidden-premise expansion even for
  papers with no explicit `Assumptions.lean` rows. In an uncached checkout this
  may be slower than a JSON export; use the export only to triage row status,
  and require the full audit/CI result before claiming there are no hidden
  premise or certificate boundaries.
- The dashboard displays the current Lean statement, the Lean-to-TeX draft, and
  the independent LLM match judgment. These LLM checks are pre-human-review
  evidence only; they do not increment `human_review.reviewed_rows`, and they
  do not replace a saved human dashboard review. Status exports include a
  `validators` ledger per row: human dashboard reviews use the saved GitHub/user
  handle with `validator_type: human`, while model/agent statement-match checks
  use the model or agent name from `statement_match_llm.json`. Keep the human
  review counter human-only; use the validator ledger for mixed human/model
  provenance, dates, judgments, stale flags, and comments.
- Do not conflate agent/formalization release readiness with human dashboard
  completion. A paper can be marked `formalized` for public status when Lean
  builds, statement/assumption validators are current, the paper-closeout audit
  passes, DAG/report evidence is current, and generated status surfaces are in
  sync, even if `0/N` saved human reviews remain. In that case the final report
  must say that human dashboard review is pending; if the user or release
  policy requires human approval, treat that as a separate promotion gate, not
  as a Lean proof gap.
- `./review-dashboard.sh` always regenerates the lightweight heuristic
  Lean-to-TeX preview from the current declarations on launch. Treat that as a
  fallback preview only. The independent statement-review workflow still
  requires stable tracked `lean_to_tex_llm.json` and `statement_match_llm.json`
  sidecars.
- On WSL2, the launcher binds broadly by default, prints localhost and any
  detected WSL guest-IP fallback, and tries to open the candidate URLs in a
  Windows browser. If one URL fails, keep the terminal running and try the
  other printed URL.
- To add `review-dashboard.sh` to existing paper folders that already have
  `PaperInterface.lean` but not the launcher yet, run:

  `python3 scripts/bootstrap_review_launchers.py --write`
- **CRITICAL MANDATE - NO HIDDEN DEFINITIONS:** A human reviewer cannot verify a theorem if its core terms are opaque references to generic library modules (e.g., `EconCSLib.Statistics.priorWeightedVariance`). The `PaperInterface.lean` file MUST expose the exact mathematical formulas for the paper's definitions. Do this by defining paper-specific `abbrev`s or `def`s at the top of the interface that spell out the raw formulas exactly as they appear in the paper, and then use those local definitions in your paper-facing theorem statements or prove they equal the generic terms. A reviewer must see the actual math equations inside this single file without needing to open imported generic modules. The same rule applies recursively through library definitions: if a reusable definition carries a paper-specific displayed formula, either expose the formula in `PaperInterface.lean` or prove and review a paper-local equivalence to it. The LLM judge sidecars must check this expanded formula surface, not just the library identifier. Keep `PostPaperAudit.lean` for theorem endpoint aliases and proof-seam coverage, not standalone proof-facing formula duplicates.
  When a paper-facing theorem depends on those formulas, state the theorem over
  the local paper definitions where practical, even if the proof immediately
  discharges the claim by `simpa` through a reusable library theorem. It is not
  enough for the formulas to appear in earlier dashboard rows while theorem
  rows still expose only opaque library terms.
  Include for each entry:
  1. the declaration name,
  2. a compact paper-style statement in comments,
  3. the key assumptions,
  4. and source location when a declaration is not a plain wrapper.
  A completed index should show the full paper-facing sequence and the final
  paper-level theorem explicitly.
- Add a structured folder `README.md` theorem-status table with columns like:
  paper theorem/definition, Lean declaration, status, file, and remaining
  assumptions/notes. Status cells MUST use the controlled vocabulary from
  `docs/STATUS.md`: `formalized`, `formalized with caveat`,
  `partially formalized`, `conditional`, `scaffold`, `not started`, or
  `not formalized`.
- **Paper Directory and Namespace Convention:** All new paper folders, modules, and internal namespaces MUST be named using the format `[AuthorInitials][2DigitYear][Descriptor]` in PascalCase (for example, `ABC12RepresentativeTitle`). This guarantees collision-proof Lean namespaces while immediately communicating the citation. All paper implementations sit within the `papers/` directory.
- **One citation per paper folder:** Do not use aggregate folders for award lists, reading lists, or multi-paper campaigns. Split them into one `[AuthorInitials][2DigitYear][Descriptor]` folder per source paper, each with its own source PDF/text cache, README, DAG, and `MainTheorems.lean`. If an aggregate module already exists, keep it only as a compatibility import or handoff note and move paper-facing status into the citation-specific folders.
- **Initial Proof Roadmap (Dependency DAG):** At the *very beginning* of formalizing a new paper, before writing any deep proof code, you must create a comprehensive proof roadmap. Read through the paper carefully to identify *every* named result (Definitions, Lemmas, Propositions, Theorems, Corollaries) and map out exactly how they relate to each other. Encode this roadmap as `DependencyDAG.tex` and render `DependencyDAG.pdf` in the paper folder; both files are review artifacts and the rendered PDF should be committed. This ensures no named result is overlooked, helps you understand the overall proof architecture, and gives humans a clear audit of the theorem flow.
  - All paper DAGs MUST `\input` the shared preamble located at `docs/tikz/dag_preamble.tex`.
  - Use the exact node styles defined in the preamble and status vocabulary:
    `formalized` uses `dag_result` (green theorem/result), `dag_lemma`
    (yellow lemma/support), or `dag_model` (blue definition/model) depending
    on node type; `formalized with caveat` uses `dag_caveat` (red diamond);
    `partially formalized` uses `dag_partial` (yellow dashed); `conditional`
    uses `dag_conditional` (orange rounded); `scaffold` uses `dag_scaffold`
    (gray dotted); and `not started`/`not formalized` use
    `dag_unformalized` (gray dashed).
  - **Green-node semantics:** A green result means the displayed paper-facing
    theorem/lemma/definition has been fully formalized under its stated Lean
    assumptions. It does not mean every lemma used in the paper's prose proof
    is independently closed. If the formal proof reaches the result by a
    different formalized path and does not need a paper lemma that remains
    partial/open, the result may be green, but the DAG must not show that
    partial/open lemma as a required solid input. Either omit that non-used
    dependency, mark it as a dashed paper-route/caveat edge, or say in the node
    or README that the paper proof input was bypassed by an alternate formal
    route.
  - If a theorem still requires an unproved assumption, certificate, or earlier
    paper lemma to obtain the paper-level statement, it is **not green**. Use
    `dag_conditional`, `dag_partial`, or `dag_caveat` as appropriate, and make
    the remaining assumption explicit in the node text and README row.
  - The whole-paper verdict must be visually consistent with the DAG. If the
    README, root table, or final report says the paper is partially
    formalized, at least the corresponding theorem endpoints must appear as
    partial/conditional/caveated nodes. An all-green DAG is inconsistent with a
    partial paper verdict unless the partial item is not represented by any
    paper-facing node, in which case the DAG inventory is incomplete.
  - **Edge semantics:** Solid `dag_arrow` edges are Lean-checked dependencies in the
    formalized proof path. Dashed `dag_dashed_arrow` edges are for paper-roadmap
    dependencies, unresolved/conditional inputs, caveat links, or dependency
    paths that are not yet fully discharged. A dashed edge into a green result
    is allowed only when it is clearly non-required for the formal proof or
    explicitly documented as a bypassed paper route; otherwise the target node
    should not be green.
    For a paper marked fully `formalized`, prefer using only solid arrows in the
    final human-facing DAG unless the diagram has a local legend/note that makes
    a non-conditional dashed meaning impossible to misread.
  - **Paper-route vs formal-route discipline:** If formalization discovers that
    a paper lemma is misstated, too strong, or unnecessary for a later theorem,
    do not silently collapse the distinction. Record the source issue in the
    README during active work and in the validation report only during
    post-validation. Keep the affected paper lemma partial/caveated, and mark
    any later theorem green only if Lean proves that theorem through a fully
    formalized alternate route or through weaker assumptions already discharged.
    If the later theorem merely assumes the problematic lemma, it is
    conditional/caveated, not green.
  - **DAG status sanity check before committing:** Reread the rendered DAG as a
    skeptical reviewer would. Every source-named proposition, theorem,
    corollary, and major definition from the paper inventory must appear; do
    not replace a missing named result with a broad topical or implementation
    bucket. A green node that is fed by a caveat, partial result, or
    conditional bridge must either state a theorem whose Lean assumptions
    visibly include that limitation, or the incoming edge must be dashed and
    clearly non-required. If the downstream source theorem is still only proved
    through certificates, finite analogues, positive-base restrictions,
    two-sided support, or other undisclosed hypotheses, mark the downstream
    theorem conditional/partial rather than green.
  - **Do not use scope notes as theorem inventory:** A prose scope note may
    clarify a diagram, but it must never be the only place where named source
    results appear. Every named Definition, Lemma, Proposition, Theorem,
    Corollary, and appendix result in `paper_statement_map.json` or the source
    inventory must be represented by a visible DAG node. Grouping is allowed
    for tightly related results, but the grouped node header must explicitly
    name the included source results, for example `\textbf{Cor. C.1-C.2;
    Lemmas C.6-C.8}`. At closeout, compare the source inventory against DAG
    node headers and treat any result that appears only in a scope note as
    missing from the DAG.
  - **Blueprint/source-map consistency:** Treat the DAG as a human-readable
    view over the source-block map, not as the source of truth. Before closeout
    or any public-facing handoff, cross-check three inventories: source-block
    map, `PaperInterface.lean`/review dashboard rows, and DAG nodes/edges. Every
    source-named paper result should have exactly one paper-facing row or an
    explicit reason for omission, every paper-facing row should trace back to a
    source block, and every required source dependency should either appear as
    an edge or be documented as an intentionally omitted redundant edge. If a
    script or table can generate the node/edge inventory, prefer that over
    maintaining duplicate hand-written lists; still inspect the rendered DAG for
    readability.
- **DAG Formatting and Clarity Mandates:**
  - **Visual Iteration Requirement:** After every substantive DAG edit, render the DAG, inspect the visual output, and keep adjusting layout until you can explicitly confirm that it looks clean with no box, legend, note, edge, or label overlap. Do not claim the DAG is done if you have not visually checked it or if any overlap remains.
  - **Minimum Node Spacing:** Keep visible whitespace between neighboring DAG
    nodes. As a default floor, leave at least about `0.6cm` between node
    bounding boxes and use larger gaps for dense text boxes, long labels, or
    high-traffic edge lanes. If arrows must pass between nodes, reserve a clear
    routing lane rather than squeezing the arrow through text or nearly touching
    boxes.
  - **Stable Topology Requirement:** The initial DAG should contain the paper's full named-result structure: all named Definitions, Lemmas, Propositions, Theorems, Corollaries, and appendix results, with dependency arrows reflecting the paper proof architecture. After that initial roadmap is created, routine progress updates should normally change only node status/style/text, not add new boxes or arrows. Add or remove boxes/arrows only when the initial named-result inventory was incomplete or a genuine paper dependency was discovered to be missing/wrong; if topology changes, rerender and re-check for overlap.
  - The DAG must encode formalization status and node type explicitly by using the preamble styles.
  - **Node Content:** Node text MUST begin with a bolded header indicating the Theorem/Lemma/Definition name and, if available, its location in the paper (e.g., `\textbf{Theorem 1 (Section 4)} \\ Description` or `\textbf{Lemma 12 (App. E)} \\ Symmetry reduction`). Provide a brief, readable description on the following line(s).
    Do not include internal source-TeX labels, Lean declaration names, helper
    theorem names, or citation keys in DAG node text. Labels such as
    `thm:...`, `lem:...`, and `source_...` belong in `PaperInterface.lean`,
    README rows, audit ledgers, or final reports, not in the visual DAG.
    Before accepting a DAG, mechanically scan the node text for `\texttt`,
    underscores, CamelCase record/theorem identifiers, and Lean-style prefixes
    such as `theorem1_`; any remaining instance must be paper notation rather
    than an implementation name.
    Treat this as a closeout audit requirement, not a cosmetic preference. If
    the DAG communicates through Lean function names, certificate type names, or
    implementation route labels, the paper is not public-ready until the DAG is
    rewritten in source-paper language and rerendered.
  - **Closed theorem text stays short:** Once a theorem is closed, the theorem
    node should describe the source theorem's statement, not the Lean proof
    machinery that closed it. Do not fill a closed theorem box with internal
    helper names, certificate layers, construction details, or a list of every
    bridge lemma. Also omit old compatibility/sufficient routes and alternate
    proof attempts from the visual node. Put those details in private proof
    notes, proof comments, or the final report during post-validation.
    Include the actual source-facing conclusion or a faithful short formula
    summary in the DAG node itself so a human can recognize the paper result
    without opening the Lean file. For example, a closed Gaussian lemma node
    should say that the posterior estimate has the displayed weighted-mean
    formula and normal law, not merely that "Gaussian algebra was proved."
  - **Source notes are not DAG caveats:** Do not put source-inventory,
    source-version, or source-convention explanations into the DAG as large
    note boxes when the paper result is otherwise closed. The visual DAG should
    show source-facing theorem nodes, reusable/library dependencies, and genuine
    unresolved boundaries. Put source-version crosswalks, convention notes,
    proof-route commentary, and source-inventory details in
    `FINAL_VALIDATION_REPORT.md`, `POST_FORMALIZATION_AUDIT.md`, status files,
    or short captions instead. A DAG note box can make a closed result look
    caveated, so use one only when it identifies an actual remaining assumption,
    source gap, or unresolved proof boundary.
  - **Keep theorem families together:** Parts of the same source theorem
    (`Theorem 2(i)`, `Theorem 2(ii)`, `Theorem 2(iii)`) should be visually
    grouped in the same column, row, or labeled cluster. Do not scatter theorem
    parts around auxiliary boxes in a way that makes the source theorem hard to
    read as one result.
  - **Named results are mandatory; auxiliaries are subordinate:** Every named
    paper Definition/Lemma/Proposition/Theorem/Corollary must appear unless the
    source inventory confirms there are none of that kind. Paper-unnamed
    implementation layers, reusable Lean primitives, certificate packages,
    feature-map plumbing, and finite analogues should usually not be primary
    DAG nodes. Add them only when they are the exact remaining caveat or are
    needed to make the named-result dependency legible, and keep them visually
    subordinate to the source-named theorem/lemma nodes.
  - **Legend:** You MUST include a Legend using the shared helper macro from the preamble, e.g., `\daglegend{(legRes)(legLem)(legDef)(legOpen)}{Legend}`. Place legend nodes concisely at the top. For caveat entries inside the legend, use `dag_caveat_legend` rather than combining `dag_caveat` with `dag_template_legend`; the full-size red diamond is for graph nodes and makes the legend oversized.
  - **Rendered inspection is required:** After changing a DAG, render the PDF
    and inspect an image conversion. Check for legend/source-node overlap, arrow
    collisions that obscure labels, stale caveat/open-boundary styling, and
    Lean declaration names in node text. Do not rely on successful LaTeX
    compilation as proof that the DAG is human-facing.
  - **Edge Routing (No Overlaps):** Use explicit positioning (`node distance`, `below=of`, `right=of`, `xshift`, `yshift`) carefully. **Prefer straight paths or simple orthogonal routing (`|-`, `-|`) whenever possible without overlap.** Use a column-based layout (the preamble standardizes horizontal spacing at `3cm` or `4cm` depending on the specific diagram needs) to ensure paths are clear and text boxes do not collide. Only use complex curves (`to[out=..., in=...]`) or bends when absolutely necessary to route around an immediate obstacle. Use `dag_arrow` and `dag_dashed_arrow` from the preamble for styling.
  - For dense paper DAGs, prioritize a visually auditable named-result topology
    over drawing every redundant instantiation arrow. If a theorem node already
    states that it satisfies particular definitions or conditions, it is
    acceptable to omit duplicate long cross-edges when those edges would create
    text or box overlap; keep the exact status and remaining assumptions in the
    node text and `status.json`/final report.
- Keep the DAG updated after every major paper update (for example: a named
  paper theorem/lemma closed, a dependency refactor that changes proof flow, or
  a status transition in the controlled status/DAG vocabulary).
- Keep the paper DAG paper-facing. Its primary nodes should be the source's
  named definitions, lemmas, propositions, theorems, and corollaries. Do not
  replace a source theorem with internal implementation layers such as finite
  analogues, certificate packages, or continuous instantiation steps unless the
  source itself is organized that way. Put those engineering layers in private
  proof notes, proof comments, or the final report, and use the DAG to show how the
  paper's named results relate and which of them are formalized, conditional,
  caveated, or open.
  Do not include empirical, numerical, simulation, benchmark, data-study, or
  reproducibility-artifact sections as DAG nodes. The DAG is a proof/theorem
  roadmap, not a full paper outline. If the source paper has a substantial
  empirical or numerical section, mention that scope explicitly in the README or
  final validation/formalization report and say it is not a Lean theorem target.
  If the source has only a few named results, keep the DAG correspondingly
  simple; do not compensate by adding a large set of paper-unnamed Lean helper
  nodes.
  Even when the working proof closes a finite analogue first, the DAG should
  still show the corresponding source theorem node with the honest paper-level
  status; finite versions belong in Lean helper names, README rows, or proof
  comments, not as replacement DAG nodes.
- If a finite analogue, certificate endpoint, or regularity-heavy wrapper is
  the current strongest Lean result, do not mark the source theorem
  `formalized with caveat` just because the wrapper compiles. Use `conditional`
  for the wrapper and `partially formalized` for the source theorem until the
  extra hypotheses are derived from the paper's primitive assumptions.
- A downstream theorem node may use the green `dag_result` style only when its
  paper-facing statement is closed without remaining paper assumptions. If Lean
  currently proves only wrappers conditional on certificates, no-gap hypotheses,
  selected-BFS assumptions, or witness existence, use `dag_conditional` for the
  wrapper and add a separate `dag_unformalized` node for the full paper theorem.
  The node text must name the exact open certificates or witnesses.
- For probabilistic papers, distinguish the source's random-variable/probability
  statement from any density, CDF, or integral representation used in the proof.
  If Lean closes the integral or closed-form layer but has not yet proved the
  measure-theoretic bridge from `Pr[...]` to that integral (for example, an
  independence/Fubini/density derivation), keep the theorem conditional in
  `status.json`, the DAG, and the final report, and explicitly name the
  probability-to-integral bridge that remains.
- For stochastic-process convergence results, do not translate a source proof
  that concludes "with probability 1" into a deterministic per-path theorem
  unless the paper explicitly proves the deterministic statement. If Lean has
  only the post-concentration skeleton, expose the remaining boundary as the
  exact concentration/escape theorem (for example, Hoeffding plus almost-sure
  escape), not as a hidden drift or direction-field field.
- For sequential weighted without-replacement or "first distinct draw" models,
  load `references/proof-foundations-probability.md`; for matching-specific
  weighted-list details, also load `references/proof-markets-social-choice.md`.
- When a proof step invokes an external cited analytic theorem that is not in
  Mathlib, encode that input as a named paper-local hypothesis or definition
  (for example, a `Sampford...Bound` assumption), prove the source's downstream
  reduction from that exact hypothesis, and keep `status.json`/DAG conditional
  until the cited theorem itself or an acceptable imported library theorem is
  formalized.
- When such a cited theorem is later formalized locally, immediately update
  `status.json` and the DAG to remove that exact assumption while preserving
  any broader remaining bridge. For example, if a scalar density/integral layer is now
  unconditional but the source theorem is still a probability statement, mark
  the scalar layer as closed and keep only the probability-to-integral bridge as
  the theorem-level blocker.
- In this repository's public `papers/[Paper]/docs/DependencyDAG.tex` layout,
  the shared preamble input is
  `\input{../../../docs/tikz/dag_preamble.tex}`. Render from the paper `docs/`
  folder (`cd papers/<Paper>/docs && latexmk -pdf DependencyDAG.tex`) or use
  `scripts/compile_dependency_dags.sh`; running `latexmk
  papers/<Paper>/docs/DependencyDAG.tex` from the repo root resolves the
  preamble relative to the wrong directory and wastes a build cycle. Verify the
  DAG renders after changing the preamble path or moving a paper folder.
- Use the shared DAG header helpers instead of manual coordinate shifts:
  `\dagPaperMetadata` for the top-left source block,
  `\dagPaperLegendRightOfMetadata{...}` for the legend row to its right, and
  `\begin{dagPaperBody}...\end{dagPaperBody}` for relative-positioned graph
  nodes below the header. Avoid the old
  `dagPaperMetadata.north east -| 0,0` pattern; it places the legend back at
  the page origin and causes overlap. After rendering, check the standalone
  crop: if graph nodes extend left of the metadata block, add a local
  `xshift` inside `dagPaperBody`; the metadata should remain the visual
  top-left anchor, with the legend to its right and the graph below.
- If a theorem is only conditional, the private README/plan and public
  `status.json`/final report must name the exact certificate or assumption
  declaration that remains. Do not describe it vaguely as "technical details".
- Distinguish certificate interfaces from certificate assumptions. A
  paper-local certificate/interface structure is just a formal proof boundary:
  it is an **assumption** only when the paper-facing theorem still takes an
  inhabitant or hypothesis as an explicit input. It is **discharged** when the
  paper folder constructs the witness/certificate and the final paper-facing
  wrapper applies it internally. `status.json`/DAG/final-report status must say which case holds.
  Auxiliary explicit-input variants are fine, but they must not make the source
  theorem look closed unless there is also a closed wrapper that no longer
  exposes those inputs.
- Use source-numbered paper declaration names only for statements that are
  source-faithful. If Lean proves an auxiliary finite analogue, certificate
  interface, or deliberately weakened bridge, name it as an auxiliary
  declaration (for example `paper_aux_*` or a name that explicitly says
  `finite_analogue`) and mark the source theorem as partial/open in
  `status.json` and the DAG.
- The private paper `README.md` or `FORMALIZATION_PLAN.md` is the live status
  ledger and handoff document for partial progress. A
  `docs/FINAL_VALIDATION_REPORT.md` is not a handoff note; it is
  the concise human assessment created only when making a final claim
  about a paper, or when the user explicitly asks for post-validation of a
  completed proof phase. It must answer whether the paper is formalized, what
  additional assumptions were needed, whether mistakes were found, and whether
  the Lean proof followed the paper strategy or used a different route. Keep it
  short and paper-facing; move long operational ledgers, status-report
  transcripts, source-line inventories, and verbose boundary details to
  `docs/POST_FORMALIZATION_AUDIT.md`, private source-audit/handoff notes,
  `PostPaperAudit.lean`, or the private README/plan as appropriate. When
  creating or updating a final validation report, also update the front
  repository `README.md` paper-status table and
  `docs/ECONCSLEAN_CURRENT_STATUS.md` so the public entry points match the
  paper-local verdict.
- For paper-specific status questions, `status.json`,
  `docs/DependencyDAG.tex`, paper-facing theorem files, private status notes
  when present, and current targeted Lean build are the source of truth. Older
  author-wide notes or campaign reports are historical/secondary and may be
  stale; never use them to override paper-local status/DAG plus successful
  build.
- **Post-paper audit protocol:** Before claiming that a paper is done, create
  or update a paper-local final audit. Do this even if status, DAG, report,
  or successful build already exists; those artifacts are not a substitute for
  the importable audit ledger. The audit must check all four artifacts:
  the source paper via local ignored cache or source URL, `status.json`,
  `docs/DependencyDAG.tex`, and the
  paper-facing Lean file(s).
  Before running this closeout, refresh the active workflow instructions from
  the repository you are publishing from, especially after another agent or
  recent pull changed audit scripts or skills. A prior successful closeout under
  an older protocol is not evidence that the current protocol is satisfied. If
  the current gate requires an independent holistic source audit, source-record
  sidecar, rendered-DAG inspection note, or other paper-local artifact, create
  that artifact and rerun the targeted closeout audit before opening or updating
  a public PR.
  - Source check: search the cached text for every named paper `Definition`,
    `Lemma`, `Proposition`, `Theorem`, and `Corollary` using a concrete search
    such as `rg -n "THEOREM|Theorem|LEMMA|Lemma|COROLLARY|Corollary|PROPOSITION|Proposition|DEFINITION|Definition" <cached-text>`.
    If a public checkout omits the cache, recreate an ignored local extraction
    from the recorded source URL before the audit rather than committing the
    generated paper text. List the source line or section in the audit report,
    and say explicitly if no numbered definitions/propositions were found.
  - Status check: every named source item must have a row using the controlled
    status vocabulary from `docs/STATUS.md`, and every non-`formalized` row must
    name the exact remaining declaration, certificate, or reason for deferral.
  - DAG check: every named result node must have a style consistent with the
    status row. Solid arrows mean Lean-checked dependencies; dashed arrows
    mean paper-route/context links or unresolved dependencies. A green node with
    a dashed incoming edge is allowed only if the status/audit says the dashed
    edge is not required by the formal proof.
  - Lean check: create a compiling `PostPaperAudit.lean` or equivalent ledger
    in the paper folder. It must be importable from the paper root module and
    expose one source-numbered audit theorem per final paper endpoint. Prefer
    raw assumption lists in the audit theorem signatures; if a paper-model
    structure is used, the docstring must state the exact paper convention that
    the structure packages. The theorem body should be a thin call to the
    paper-facing declaration, so a human can inspect the endpoint in one file.
    Do not mark the paper complete until the root module imports this ledger.
  - One-stop endpoint check: for each main theorem, expose at least one audit
    wrapper whose conclusion is the paper-level result a human expects to read,
    not only internal component lemmas. If the proof naturally produces an iff,
    certificate, or witness, also add direct wrappers such as named-witness
    existence, `∃!` uniqueness, bundled conclusion endpoints, and componentwise
    equality statements for opaque structures. For dynamic games or mechanisms
    with named strategies/witnesses, also add pointwise behavior equivalences,
    pairwise uniqueness/equality consequences, named-witness outcome wrappers,
    and any useful generic certificate constructors plus the generic theorem
    conclusion obtained from those constructors. Keep assumptions/certificates
    in the signature only when they are genuine remaining paper obligations, and
    name them explicitly in `status.json` and the DAG.
  - Report check: create or update `docs/FINAL_VALIDATION_REPORT.md` in the
    paper folder. It must state whether the paper is formalized, the exact source
    version, the named-result inventory, any deliberate model conventions or
    proof-route deviations, the commands run, and links to status, DAG, and
    audit ledger. If the report needs detailed source line mappings, helper
    theorem inventories, source-facing surface listings, or important-boundary
    implementation notes to preserve context, move those details into
    `docs/POST_FORMALIZATION_AUDIT.md` or private audit notes and summarize only the
    human-relevant conclusion in the final report.
  - Build check: after updating the audit, run the targeted paper build and
    render the DAG from the paper folder. Also run a placeholder grep over the
    claimed paper and library files, a stale-status grep over `status.json`/DAG/
    final report, and `git diff --check`. Do not mark the audit complete until
    all required commands succeed.
- **Post-formalization library elevation pass:** Once a paper theorem closes,
  scan the proof for reusable primitives, proof results, and proof techniques
  that belong in `EconCSLib` rather than the paper namespace. Good candidates
  include model-neutral definitions, algorithm trace APIs, invariants,
  side-symmetry lemmas, finite-cardinality bridges, monotonicity/termination
  facts, reusable certificate constructors, common proof decompositions, and
  tactic patterns that would help another paper. Run this pass deliberately as
  part of closeout: elevate stable reusable APIs/results before final validation
  when the extraction is local and low-risk. If the extraction would require a
  broader naming/API design pass, leave the paper-facing wrapper in place and
  record concrete migration candidates, likely destination modules, and the
  proof technique worth preserving in the final report.
- Batch paper-folder `README.md` and campaign-report updates for throughput.
  Update them when a named lemma/proposition/theorem is closed, before a commit,
  before stopping or moving papers, or after a long stretch without status
  updates (about 30 minutes). Do not interrupt every helper lemma just to edit
  docs, but do not leave a paper or checkpoint with stale `scaffold`,
  `conditional`, or remaining-assumption text; either close the seam or record
  the exact blocker and the next theorem to attack.
- Do not update the author-wide formalization report file
  `docs/GARG_AUTHOR_FORMALIZATION_REPORT.md` during routine intermediate work.
  Update it only when the paper is finished, when stopping, or when you are
  moving on to another paper.
- Commit at paper-scale checkpoints, not every small lemma. Prefer committing
  when a named theorem/proposition/lemma from the paper is proven or when
  moving on from a paper; otherwise keep related intermediate proof work
  together in the working tree. A local commit does not automatically require a
  rebase or generated-status refresh. A routine private proof checkpoint can be
  pushed without rebasing first; do not insert a rebase just because you are
  about to push. Rebase only at major milestones such as when a paper is
  finished, before publication/PR work, after meaningful public library/API
  changes, or on explicit request.
- Prioritize finishing the theorem over creating frequent checkpoints. Once the
  finite scaffold is stable, spend effort on the hard remaining bridge rather
  than packaging every helper lemma as a separate commit or documentation pass.
  Commit only when a substantial named result is genuinely closed, when moving
  papers, or when the user explicitly asks for a checkpoint.
- When a finite version of a theorem is the requested milestone, finish the
  finite public endpoint first and validate it through the paper interface.
  Only then refresh the paper-local status source, README/proof-plan/final
  report, DAG source and rendered PDF, and any skill lessons, then make one
  milestone commit and push. The documentation should state which finite
  hypotheses remain and should not imply the infinite or unconstrained source
  theorem is closed.
- Detailed lemmas may live in many files, but the central theorem file should be
  the stable public interface for that paper.

### 1.4 Context Budget and Resume Protocol

Resume from the current public interface, not from the commit history. For long
formalization campaigns, the fastest reliable map is the status docs, the paper
README theorem table, the paper-facing theorem file, and targeted declaration
search.

- Start every resumed task with `git status --short --branch`, then read the
  current repo/paper status note and the paper folder README. Protect unrelated
  dirty files, and let the documented current seam define the first theorem to
  inspect.
- If shell startup prints `Failed to create stream fd: Operation not permitted`
  before otherwise successful command output, treat it as an Ubuntu
  `im-config`/`systemd-cat` login-shell warning, not a repo failure. On Ubuntu
  images this can come from `/etc/profile.d/im-config_wayland.sh` sourcing
  `/usr/share/im-config/initializer`, whose `systemd-cat` logging fails under
  sandboxed non-systemd sessions. Confirm with `bash -l -c true` if needed. In
  Codex tool calls, use non-login shells (`login:false`, e.g. `/bin/bash`) for
  routine commands to avoid the noise; do not spend proof-debugging time on it.
- Use a five-minute resume path before opening large Lean files: read the
  paper handoff/README current-target section, `rg` the exact public wrapper
  and remaining assumption names, inspect only those theorem neighborhoods, and
  run the targeted build if the status is uncertain. This usually recovers
  context faster than reading thousands of lines or replaying chat history.
- Use targeted `rg` searches for the strongest paper-facing wrapper, the exact
  remaining certificate/assumption named in the README, and the internal lemma
  that feeds it. Avoid scanning broad proof files or docs until those anchors are
  identified.
- For huge diffs or dirty worktrees, use path-limited `git diff --stat`,
  `git status --short -- <paths>`, and narrow `git diff -- <paths>` first. Do
  not print whole-repo diffs unless the task is explicitly repository-wide.
- Treat successfully compiling declarations and current status tables as the
  source of truth for "what is done." Use commit history only for provenance,
  rename recovery, or checking what changed since a known checkpoint. If history
  is needed, keep it bounded: `git log --oneline -n 10`, `git show --stat
  <recent>`, or a narrow path-limited diff. Do not use open-ended commit
  archaeology as the default way to regain context.
- After a long interruption or a user asks whether anything was lost, perform
  the three cheap checks: worktree status, targeted declaration search, and a
  targeted `lake build <active-module>`. Do not replay old proof search unless
  those checks reveal a real gap.
- When reading context, batch independent cheap shell reads with parallel tool
  calls, but keep each output scoped: `sed` around named declarations, `rg -n`
  for exact theorem names, and `git diff --stat` before full diffs. Prefer one
  well-sized context read over many failed micro-reads when preparing an edit.
- Before saying a paper is "done" or "fully formalized," perform a paper-local
  validation pass: read `status.json` and any private theorem-status notes,
  inspect the DAG
  status for the named main results, check the paper-facing theorem file for
  the strongest closed wrappers, run the targeted `lake build <module>`, and
  search only the target Lean files for real proof placeholders such as
  `sorry`, `admit`, or `axiom`, for example
  `rg -n "sorry|admit|axiom" papers/<Paper> --glob '*.lean'`. Ignore cached
  PDF text, markdown prose, skill files, and comments when doing placeholder
  searches; otherwise ordinary instructional text creates false positives.
  If auxiliary certificate/BFS/interface theorems still take explicit inputs,
  verify that the final source wrapper does not expose them before calling the
  source theorem closed.
- After closing a paper seam, run a stale-status grep over `status.json`, the
  DAG, private status notes when present, and, during post-validation, final
  report before committing, for example:
  `rg "Previous status|not formalized|partially formalized|conditional|none for|source wrappers partial" papers/<Paper>`.
  Stale ledger wording is often the only remaining "gap" after Lean is green.
  Keep legend entries if the template includes them, but no actual paper node
  should advertise an obsolete status.
- Before editing, state the one active seam in local notes or the handoff doc:
  public theorem wrapper, internal lemma/certificate being attacked, exact
  remaining assumption, and the build command that validates the slice.
- Before building a large helper tower, write or locate the paper-facing wrapper
  and the exact bridge theorem that would close it. If the bridge is too hard,
  make the helper an explicitly named auxiliary result and record the bridge as
  the remaining seam; do not let a reduced analogue masquerade as the source
  theorem.
- Do not revisit closed layers first. Search for the strongest current endpoint
  and the precise "remaining" text, then work on that next bridge. In this repo,
  `status.json`, private status notes, and aggregate status docs should say
  which algebra, symmetry, probability, or model-integration layers are already
  closed.
- When stopping or moving papers, document "do not redo" information: closed
  theorem layers, the current endpoint, the next bridge, known traps, and the
  last passing build command. This prevents future agents from spending tokens
  re-deriving the same orientation.
- If the user asks to stop soon, first pick a named theorem/lemma endpoint that
  can be made green quickly, finish that wrapper, and run the targeted module
  plus paper-root builds. Only then update `status.json`, the DAG, and private
  handoff notes. Do not
  start a fresh hard proof branch just before documenting a handoff.
- Before committing a pause handoff, expose any newly closed internal theorem
  through the paper-facing wrapper layer if it is part of the source proof
  audit. Otherwise the next agent has to rediscover that the lemma exists
  internally. Update `status.json`, the DAG, and private status notes from
  those public wrapper names rather than from private proof-local names.

### 1.5 Workflow

1. Orient before editing.
   Read the repo README, roadmap, architecture notes, and paper-specific
   handoff documents. Identify the public theorem target and the smallest local
   lemma that moves it forward.
   For a brand-new paper, your *very first task* is to read through the paper to extract the proof roadmap. Produce the comprehensive named-result dependency DAG (capturing every definition, lemma, proposition, theorem, and corollary and their exact relationships) as a TikZ diagram using the shared preamble. This serves as your master plan to understand the paper's architecture. Keep it current through the campaign as results change status.
   Also create or refresh the source-block map before proof search: named
   result, source location, dependencies, Lean declaration, proof status, and
   reusable library candidates. Use it to choose the fastest route to overall
   completion, not merely the smallest next green lemma.

2. Context Efficiency vs. Edit Accuracy (File Reading Strategy).
   Do not over-optimize context limits by reading tiny chunks of files (e.g., using `sed` to read 15-20 lines) if you are about to use the `replace` tool. Micro-reading frequently drops necessary surrounding whitespace or context, causing the `replace` tool to fail repeatedly with "0 occurrences found". The cost of spinning in a multi-turn failure loop is far higher than the cost of reading the entire file once. Use `read_file` to ingest small-to-medium files completely, or use `grep -C 20` to get substantial context, ensuring you capture exact, copy-pasteable blocks for your `old_string`.

3. Stabilize the build first.
   Run targeted `lake build <module>` commands before making broad changes. Fix
   dependency, import, or cache problems before interpreting downstream proof
   errors.
   During proof work, use a compiler-guided repair loop: make one candidate
   statement or proof edit, run the narrowest Lean check that exercises it,
   inspect the first concrete error and goal state, then repair locally under
   the fixed paper-facing signature whenever the source translation is already
   correct. If the same failure recurs, split out the missing lemma, retrieve a
   similar proof/API, or record the failed route in the handoff rather than
   repeatedly changing the public theorem target.

3. Choose the model level that closes the theorem fastest.
   EC papers often have useful finite entry points: finite agents, items,
   actions, rankings, allocations, mechanisms, PMFs, and finite sums. Use those
   when they expose the key combinatorics cleanly. But do not force a finite
   analogue first if the paper theorem is genuinely continuous, stochastic, or
   measure-theoretic and the direct source statement is shorter, more faithful,
   or necessary to finish the paper. In that case, state the continuous objects
   directly: measures, Bochner or Lebesgue integrals, almost-everywhere claims,
   densities, stopping/renewal assumptions, CTMC transition probabilities, and
   long-run reward limits should be first-class Lean targets rather than
   deferred prose. For proof-specific tactics, load the relevant reference in
   Component 2 instead of putting those techniques in this main workflow file.
   The priority order is: close the paper-facing theorem faithfully, choose the
   quickest model level that makes the proof work, and extract reusable tools
   only when they clearly help this proof or a near-term second paper. A finite
   scaffold is a tool, not a required first phase.

4. Extract shared primitives into the main library.
   Reusable finite expectations, policies, allocations, valuations, mechanisms,
   rankings, conditional expectations, graph lemmas, and sign lemmas should live
   in main library modules, not buried in one paper folder. Keep only
   paper-specific definitions and wrappers in paper namespaces.
   Build the reusable abstraction at the point it accelerates the active paper:
   do not spend a session polishing general infrastructure whose first real use
   is still speculative.

5. Make every paper pay library rent.
   When a proof needs a reusable object, add the general version once and reuse
   it. Avoid parallel versions of allocations, randomized policies, mechanisms,
   expectations, graph reachability, or inequality certificates in each paper
   folder.

6. Prefer compileable partial progress.
   If the full main theorem is not ready, add definitions, local invariants,
   certificate structures, and conditional theorems that compile. Avoid `sorry`
   unless the user explicitly asks for placeholder theorem statements.
   Treat this as a checkpoint discipline, not a destination. After a
   conditional theorem compiles, the next default task is to discharge its
   certificate/hypothesis inputs by deriving them from the source model or to
   route true paper assumptions through `Assumptions.lean` and the
   assumption judge. Do not keep building more conditional wrappers around the
   same open premise.
   If Lean exposes that a paper lemma is false as stated, do not silently weaken
   the paper-facing declaration to make progress. State the paper version, prove
   the strongest true nearby lemma separately, and add a small compiled
   counterexample theorem when possible. Mark the README/status row as a
   validation issue with the exact failed hypothesis or inequality.

7. Document exact theorem seams.
   When stopping mid-proof, record the module, theorem, assumptions still
   missing, commands run, the next lemma to prove, and any closed layers that
   should not be revisited. Future agents should not have to rediscover the
   proof state. Include useful failed proof attempts, Lean error patterns, and
   successful repair lemmas when they would help future retrieval or prevent the
   same dead end. If a paper is plausibly beyond the current model's effective
   proof-search capacity, make that explicit in the private handoff and public
   status:
   name the reduced target, record failed/counterexample-search evidence, and
   mark it as a future stronger-model pickup instead of leaving an ambiguous
   stale conditional theorem. Also update the root `README.md` and
   `docs/ECONCSLEAN_CURRENT_STATUS.md` in the same pass so the public project
   front door matches the paper-local pause verdict.

8. Verify narrowly, then broadly.
   First build the touched module. Then build the parent paper root. Run full
   `lake build` for release/integration checks.

9. For long-running branches with many sessions, avoid broad history archaeology.
   A fast resume loop is: (`git status --short --branch`), inspect the paper
   README + paper-facing theorem file, verify the latest build command in the handoff
   doc, and only then do targeted `rg`/`lake build` steps.

10. For author-wide paper campaigns, maintain a running markdown report.
   Record every paper screened, the source version, venue, author-position
   decision, theorem-status decision, declarations added, blocker if any, build
   command, and commit hash. Do not advance from a paper until either its main
   theorem interface is closed without `sorry`/conditional assumptions or the
   report states the precise bug/too-hard reason blocking faithful
   formalization.
   Update this report only at paper completion, at explicit handoff boundaries,
   or when stopping/resuming across papers.

### 1.6 Build Hygiene and Source Control Safety

**CRITICAL MANDATE - CONCURRENT AGENT SAFETY:**
- Assume there could be other agents or human users simultaneously working on different files within the same repository.
- **NEVER** use aggressive global resets like `git reset --hard`, `git clean -fd`, or `git checkout .` unless explicitly instructed to do so by the user. These commands will permanently destroy work being done by other concurrent agents.
- **NEVER** use `git reset` of any kind in a dirty shared worktree unless the
  user explicitly requests that exact operation. Even soft or mixed resets can
  disturb other agents' staged work or branch position. Use scoped `git add`,
  path-limited commits, or follow-up corrective commits instead.
- **NEVER** use `git restore`, `git restore --staged`, checkout-based file
  rewinds, or index restaging as a recovery move in a dirty shared worktree.
  If staging or commit scope is wrong, leave the index alone and recover with a
  follow-up commit or explicit coordination. Only use ordinary scoped
  `git add path...` for files you intentionally edited.
- Use the native `apply_patch` editing tool for manual source edits. Do not
  invoke `apply_patch` through a shell command, and do not use heredoc/sed/perl
  write tricks for ordinary Lean, README, or skill edits; those paths obscure
  exactly what changed and are easy to misapply in a dirty multi-agent tree.
- Before committing, inspect `git status --short` and `git diff --name-only`.
  Stage explicit paths only, normally the active paper files plus any intended
  skill/docs updates. Do not stage unrelated dirty dependency repairs made only
  to let a local build proceed unless you intentionally take ownership of that
  library change.

- Lake reuses `.olean` artifacts when sources, imports, Lean version, and
  dependency artifacts are unchanged.
- After changing `lean-toolchain`, `lakefile.toml`, or dependency revisions,
  expect substantial rebuilds.
- If generated artifacts produce invalid headers or impossible import errors,
  clean generated dependency outputs and rebuild rather than patching random
  downstream files.
- If a direct module build succeeds but downstream imports still report that
  newly-added declarations are unknown, suspect a stale module artifact before
  doing proof search. Confirm with a cheap declaration check such as
  `strings .lake/build/lib/lean/Path/To/Module.ilean | rg declarationName`.
  If it is stale, remove only that module's generated artifacts
  (`.olean`, `.ilean`, matching `.hash` files, and the corresponding `.c`/hash
  under `.lake/build/ir/`) and rebuild the target module. Avoid broad
  `lake clean` in concurrent-agent worktrees because it wastes time and can
  invalidate other agents' caches.
- If a long build is interrupted, already-finished modules usually remain
  cached; rerunning resumes from remaining work.
- Do not start a long build of a downstream module when you are about to edit
  one of its dependencies. Build the touched dependency first, then the paper
  root after the dependency is stable.
- Do not infer that downstream files are broken until the direct imported module
  builds.
- If a focused paper build fails because an unrelated imported module is dirty,
  first ask whether a narrower import would avoid that dependency. If a small
  local repair to the unrelated file is unavoidable to continue the build,
  document it in the handoff and leave it unstaged unless the active paper
  truly depends on that repaired theorem.
- For deterministic heartbeat failures in one large proof, first replace heavy
  terminal `linarith`/`nlinarith`/`ring` calls with explicit named inequalities
  and a short contradiction chain. If the proof is still too large, use
  `set_option maxHeartbeats <n> in` scoped to that single declaration with a
  one-line comment explaining why. Do not raise repository-wide heartbeat
  limits or linter settings to mask one theorem.
- Existing warnings are not build failures unless the user asks for lint cleanup
  or the project enforces warning-free builds.
- `declaration uses sorry` messages are proof-debt warnings, not style-linter
  noise. Do not add lakefile options to hide them; either close the `sorry`s or
  keep build output scoped/tail-filtered so repeated known warnings do not fill
  the context window.
- If build logs are dominated by repeated non-actionable linter warnings,
  quiet only those specific style/noise linters in `lakefile.toml` (e.g.,
  `weak.linter.style.whitespace = false`) and record why. Do not disable proof
  checking or hide theorem errors.
- To save context during iteration, redirect targeted builds to a temporary log
  and print only the tail on failure or completion, e.g.:

```bash
lake build ABC24ShortTitle.MainTheorems >/tmp/econcs-build.log 2>&1
status=$?
tail -80 /tmp/econcs-build.log
exit $status
```

- Prefer `lake build <touched-root-module>` over full `lake build` until the
  paper slice is ready for integration.
- After shared-library edits during active paper proof work, build the touched
  library module and the active paper root. Do not broaden to full `lake build`
  until a natural stopping point: paper completion/handoff, commit/push of an
  integration batch, public PR/release preparation, or explicit user request.
- Do not start a fresh worktree or cold-cache build merely to validate closeout.
  Use the warmed worktree's targeted paper build and the required audit scripts;
  rely on CI for a clean-environment check when a public PR or release needs
  one.
- After splitting out a proof-route file, build that route module first, then
  the parent theorem root such as `PaperName.MainTheorems`. Do not broaden to a
  full `lake build` until the route import boundary is stable or the task is at
  a release/integration checkpoint.
- Do not rerun Lean after Markdown-only edits unless the user needs a fresh
  end-to-end checkpoint. After Lean edits, build the touched module first; after
  documentation edits, use `git diff --check` and stale-text `rg` instead.

### 1.7 Paper Triage

Prefer first-pass formalizations with:

- finite objects and finite sums,
- constructive algorithms with simple invariants,
- clean equilibrium, allocation, matching, ranking, or auction definitions,
- reusable primitives likely to help later papers,
- theorem statements decomposable into local lemmas.

Usually defer or isolate papers whose first main result depends on the following, unless expanding a completed core or instructed otherwise:

- large complexity-theory reductions,
- heavy measure theory or asymptotics,
- external solvers without certificate interfaces,
- long empirical pipelines,
- broad economic existence theorems before the finite library is mature.

### 1.8 Handoff Checklist

Before ending work, update a repo note or paper handoff with:

- build commands that passed or failed,
- active theorem seam,
- assumptions imported from the paper,
- shared abstractions added,
- next lemma a future agent should prove,
- closed layers and traps future agents should not re-open,
- whether commit history is needed for the next resume; usually it should not be
  if the status docs and README are current.
- enough exact declaration names that the next agent can start with `rg` rather
  than rereading the proof session transcript.

### 1.10 Token Efficiency and Mathlib Discovery

**CRITICAL MANDATE - DO NOT GUESS MATHLIB LEMMAS:**
When you need a Mathlib lemma (e.g., for `Filter.Tendsto`, `Finset.sum`, or topological limits), **DO NOT guess its exact camelCase or snake_case name in a loop.** This wastes massive amounts of tokens and context window.
Instead:
1. Create a minimal `/tmp/test.lean` file that imports only the touched module
   or the narrow Mathlib leaf you are testing.
2. State the exact theorem you want to prove.
3. Use the `exact?` or `apply?` tactics inside the proof.
4. Run `lake env lean /tmp/test.lean` to let Lean's internal search engine give you the exact lemma name.
5. If `exact?` fails, search the local `.lake/packages/mathlib` repository
   using `rg` for keywords, or use `Moogle` / LeanSearchClient if configured.
6. If the scratch proof requires a new import, add the narrow leaf import at
   the file that uses the declaration; do not recover by importing aggregate
   roots such as `Mathlib` or `EconCSLib`.

Never enter a cycle of modifying a single line in a shell command just to test slightly different lemma names. Stop, use `exact?`, and proceed efficiently.

Before declaring a paper "done," or when the user explicitly asks for
post-validation of a completed proof phase, run a final human-facing validation
pass:

- Re-read `PaperInterface.lean` and check each named
  definition/theorem/corollary against the paper statement.
- Run the paper-local review workflow from within the paper folder:
  `./review-dashboard.sh` and record checks/note any uncertain matches in the
  dashboard before finalizing. If you changed interface statements after earlier
  checks, the launcher surfaces stale warnings so you can refresh only the affected
  items. Use `./review-dashboard.sh --check` to run the precheck step in CI-like,
  non-interactive mode before handoff.
- For non-final proof loops and short pauses, do not treat dashboard refresh as
  required validation. A successful focused Lean build plus a precise handoff
  note is the right stopping boundary; run dashboard refresh/precheck only when
  the next action is human review, release/finalization, or a broader audit.
- Confirm every final paper-facing declaration is fully formalized with no
  hidden placeholders; no unresolved `sorry`, scaffold wrappers, or unnamed
  gaps should remain in the claimed result chain.
- When a statement looks stuck because a source paper leaves a routine domain
  condition implicit, identify the mathematical assumption instead of adding
  wrappers around the obstruction. Human papers often silently rely on positive
  denominators, nonzero measure/mass, bounded support, integrability, nonempty
  feasible sets, interior capacity, full support, or quantities being bounded
  away from zero. If adding that assumption would make the theorem much easier
  while preserving the intended source claim, add it explicitly to the Lean
  statement, mark the result conditional if needed, and surface the decision to
  the human in `status.json`, the DAG, and the report rather than spending days on a stronger
  all-domain theorem.
- If a result remains conditional, ensure assumptions/certificates are explicit
  in both the theorem statement and `status.json`, with exact declaration names
  and no vague wording.
- Produce a final human-facing report in the paper folder alongside the DAG
  artifacts (TikZ source and rendered image). This report is not for routine
  handoff or an implementation inventory. It is the concise final assessment a
  human should read to decide whether the paper's definitions and named theorem
  statements were represented correctly.
- If the final status is `formalized with caveat` because a closed Lean result
  intentionally differs from the paper due to a real source discrepancy, also
  create a concise caveat-repair memo. Prefer a tracked TeX source plus rendered
  PDF: start with a 1--2 page executive summary, then give a deeper note for
  each issue in human-facing proof language. Do not fill the memo with Lean
  declaration names. For algebraic/formula caveats, state the old source
  equation, the exact replacement equation, the source theorem/proposition
  locations affected, and a short TeX derivation explaining why the replacement
  is correct. Update that memo when the human gives feedback.
- In the source-caveat pass, audit proof prose as well as theorem boxes. Trace
  normalized quantities through the next comparison whenever a source symbol
  could mean an admitted-class share, group-conditional admission probability,
  probability mass, capacity-normalized share, or objective contribution. If a
  proof line compares a quantity under the wrong normalization but the final
  Lean theorem uses the correct source theorem statement, record this as a
  proof-text/source-notation repair in the caveat memo and final report. Do not
  call the Lean theorem wrong unless the formalized statement itself depends on
  the bad comparison. For example, if `tau_g` is defined as `pi_g` times a
  selected mass divided by total capacity, then `tau_g` is an admitted-class
  share. Underrepresentation is `tau_B < pi_B` or an equivalent
  group-conditional-rate comparison, not raw `tau_B < tau_A` unless equal
  population shares or another explicit normalization has been assumed. When
  the Lean endpoint uses `tau_B < pi_B`, classify the raw-comparison sentence
  as a proof-text repair only.
- Formula-bearing reviewed rows in `PaperInterface.lean` must have an explicit
  `Source status:` line in the paper-facing comment. Use short labels such as
  `Source status: derived from source primitives.`, `Source status: paper
  theorem from source conditions.`, or `Source status: formalized source note.`
  Do this before regenerating sidecars; the closeout audit treats missing
  provenance lines as errors for formalized papers.
- Do not put broad package constructors, certificate records, or imported
  wrapper aliases in the reviewed surface merely because they are useful
  summary endpoints. If a row returns a package/record/consequence type rather
  than displaying the source formula or theorem subclaim directly, classify it
  as auxiliary unless the report and source-map make the package fields
  explicit and the audit accepts the row. Keep reviewed rows on displayed paper
  formulas, named theorem endpoints, and exact source conditions.
- Treat the final validation report itself as an audit target. Before final
  handoff, reread the report as a human reviewer would: it must be paper-facing,
  short enough to inspect, organized around source definitions and named theorem
  boxes, explicit about what remains for human dashboard review, and free of
  stale blocked-command language. If it reads like a helper-theorem ledger,
  proof-script changelog, or shell transcript, rewrite it before claiming
  post-validation is complete.
  Put source-convention details, source-record field inventories, and
  warnings meant mainly to prevent future agent confusion in
  `POST_FORMALIZATION_AUDIT.md` or another agent-facing note. Include them in
  the human-facing final report only when they change the theorem statement,
  require an additional assumption, identify a source-paper issue, or explain a
  real remaining boundary.
  The report and DAG are also machine-audited closeout artifacts. A paper at a
  final closeout status, including an intentionally conditional/approved-boundary
  closeout, must have a current DAG audit/status section, validation checks
  section, explicit `DependencyDAG.tex` and `DependencyDAG.pdf` evidence,
  rendered/visual inspection notes, and the targeted `audit_repository.py
  --paper <paper-folder> --paper-closeout --include-active --info-limit 0`
  command. Run that audit after editing the report or DAG at closeout; do not
  rely on prose memory that those checks happened. Use `--paper-closeout` for
  completion claims so unrelated paper-folder maintenance cannot mask this
  paper's status, but do not apply this paragraph to an unfinished active paper
  merely because it is temporarily conditional or partially formalized.
  Follow the current report template order, not an older partially reorganized
  report. In particular, keep the paper-interface review sections at the end:
  `Paper Definitions Checked`, `Named Theorem Statements Checked`, and
  `Paper-Facing Statement Validator Ledger`. Do not leave placeholders or
  pointers saying where those sections belong; move the text into template
  order and fill the validator ledger from the dashboard export.
  In a public-repo batch cleanup, audit reports one by one and run an exact
  heading-order check across every `papers/*/FINAL_VALIDATION_REPORT.md` before
  committing. Also scan for pointer prose such as `See the verdict...`,
  `where those sections belong`, `to be filled`, `TODO`, or `TBD`; every
  template section should contain final human-facing content, even if that
  content is simply `None`.
- Write the final validation report in paper language, not Lean-internal
  implementation language. Near the top it must answer four questions directly:
  what has been proved, whether formalization found anything wrong or ambiguous
  in the paper, whether any qualitatively different proof/modeling route was
  needed, and what remains for Lean versus human review.
  Keep the "what has been proved" answer outcome-focused. If every source
  definition and named result is closed, say concisely that the paper is fully
  formalized. Do not fill this section with process statements such as
  `Theorem X no longer takes external witnesses` or `the representation is now
  derived internally`; those are implementation-route notes, not final
  human-facing proof claims.
- Human-facing documentation should describe current status, not the route by
  which that status was reached. In DAGs, READMEs, final validation reports,
  generated status summaries, and coauthor-facing memos, avoid history markers
  such as `no longer`, `previously`, `now`, `formerly`, `superseded`,
  `restored`, or `old route`, unless the historical comparison is itself a
  source-paper caveat or an explicit user-requested retrospective. A human
  reviewer should see the current theorem statement, current proof status,
  current caveats, and current remaining boundary. Put implementation history,
  abandoned routes, and route-change notes only in Codex-facing handoffs,
  proof-plan scratchpads, or commit messages when they help future agents.
- Include a Lean footprint in every final validation report: total lines across
  paper-local `.lean` files, the line count of `PaperInterface.lean`, and the
  number of human-review rows/declarations exposed there. Use this to make the
  scale of the proof and the size of the review surface clear to humans.
  The total paper-local `.lean` line count is the full proof footprint and is
  the value exported as `lean_loc`/`Full proof LOC`; it is intentionally
  different from the smaller `PaperInterface.lean` line count. Never use the
  interface line count as the paper proof LOC in generated manuscript, docs, or
  website tables.
- Include a short "proof tricks worth reusing" section in the final report.
  This should be a durable engineering summary, not theorem-specific proof
  chatter: name the modeling choices, proof decomposition, and Lean tactics or
  library seams that saved time or would have saved time if used earlier.
- Run a proof-level library-lift pass before final handoff. Inspect the
  paper-local proof modules for thin wrappers around `EconCSLib`, generic
  lemmas that are not paper-specific, reusable certificate constructors,
  proof-result patterns, and techniques that would serve another paper. Extract
  small, targeted generic lemmas/results immediately when the destination is
  clear and the build can be checked; otherwise record the candidate,
  destination module, and reusable proof idea in the final report. Do not
  perform a risky broad move during final closeout.
  After extraction, rebuild both the new leaf modules and the paper target that
  imported or inspired them. If a paper-local proof relies on unfolding a raw
  arithmetic formula or `if` expression, keep the source-shaped local formula
  in the paper namespace and make the shared API a reusable sibling rather than
  replacing the local declaration with an opaque one-step alias.
- Run a skill-update pass as a required post-formalization step. If the paper
  taught a reusable workflow lesson, update this skill or its reference files
  before final handoff; if it did not, state that explicitly in the final
  report or handoff. Put durable process rules in this always-loaded file only
  if they apply across papers, and put theorem-family, domain, or proof-pattern
  details in the appropriate reference file.
- Include a final DAG audit in the final report. Confirm the DAG was rendered
  and visually inspected, note any topology changes, and state whether the DAG
  has missing/extra paper-facing boxes, node-overlap, label-overlap, or
  arrow-through-text issues.
- Before writing that report, do a statement-surface pass outside Lean: list
  every paper definition/object and every named result in source order, decide
  which Lean declaration should be the reader-facing statement for each one,
  and note any source imprecision or proof deviation. Keep this plan current as
  proof work progresses; do not wait until the end to reconstruct the theorem
  inventory from helper lemmas.
- Before final handoff or publish, require current tracked LLM sidecars for the
  curated target-paper surface. `lean_to_tex_llm.json`,
  `statement_match_llm.json`, `paper_coverage_llm.json`,
  `review_surface_llm.json` when threshold-triggered, and
  `assumption_match_llm.json` for all `assumption_names` and
  `proof_boundary_names` must be present and non-stale according to the Python
  prechecks. This does not require rerunning judges for unchanged rows or for
  unrelated papers. If any target-paper sidecar is missing, stale, or
  reports `uncertain`/`mismatch`/`partial_boundary`, the final report must list
  the exact rows and the paper status must remain conditional/partial as
  appropriate. For a strict statement `mismatch` that is intentionally accepted
  because of an external/library/analytic boundary, the sidecar must keep
  `judgment: "mismatch"` and add `resolution: "conditional_boundary"` with the
  named boundary and conditional premises; the final report should count it
  separately from unresolved mismatches. Do not treat a green Lean build or a
  clean `#print axioms` pass as a substitute for these LLM-as-judge artifacts.
- For completed papers, ensure `PaperInterface.lean` is compact enough for a
  human review session. As a default audit threshold, it should normally have
  tens of declarations, not hundreds; if it needs slices to be navigable, it is
  probably serving the wrong role. It should mirror the DAG: paper definitions
  first, with the actual formulas visible in the file, then direct theorem
  statements matching the paper. It must not be only an alias list, witness
  tuple, or pointer layer to `MainTheorems.lean`; a human should be able to read
  this file alone and check that the encoded definitions and theorem statements
  reflect the source text. Proofs may be short calls into the implementation
  layer. Keep exhaustive aliases and auxiliary seams in `PostPaperAudit.lean`,
  not in the interface.
- In `PaperInterface.lean`, aim for one declaration per paper definition or
  formatted paper object, and one declaration per named result or numbered part
  of a named result. If a theorem box has parts (i)--(iii), separate direct
  declarations are acceptable when they mirror those source parts and avoid
  noisy tuple witnesses.
- Before launching the dashboard, do a quick size check:
  `wc -l papers/<Paper>/PaperInterface.lean` and
  `rg -c '^(noncomputable\\s+|private\\s+|protected\\s+)*(theorem|lemma|def|abbrev) ' papers/<Paper>/PaperInterface.lean`.
  If the declaration count is in the hundreds, split implementation endpoints
  out before asking a human to review it.
- If `PaperInterface.lean` starts to grow, split broad proof/API aliases into
  `ProofInterface.lean` or implementation modules. Curate the review rows and
  optional slices in paper-local `status.json` under `review_surface`, then run
  `python3 scripts/sync_paper_status.py` to refresh `papers/status.json`,
  `papers/human_status.json`, `docs/PAPER_STATUS.md`, the root README status
  table, and the site status table; after that, refresh the ignored dashboard
  cache. Do not confuse "0/N reviewed" with stale or failed Lean validation; it
  only means no human review entries have been saved.
  Final human review should normally expose a compact source-facing surface,
  not every proof endpoint. Do not report an unfiltered declaration count such
  as hundreds of rows as the human dashboard surface in a final validation
  report; fix the interface first and report the curated count.
- Treat `PostPaperAudit.lean` as the exhaustive importable ledger, not the
  readable paper interface. Its header should say that explicitly and point to
  `PaperInterface.lean` for the DAG-shaped human-facing surface. It should
  contain source-numbered theorem aliases, named-result wrappers, and supporting
  proof-seam endpoints when those seams are useful for auditing the named
  claims. Do not add standalone proof-facing formula aliases when the formulas
  already appear in `PaperInterface.lean` or are only internal implementation
  plumbing.
- For papers already marked `Formalized` or `Formalized with caveat`, backfill
  the same post-paper surface instead of leaving older
  validation artifacts in place: a readable `PaperInterface.lean`, an
  exhaustive `PostPaperAudit.lean` endpoint ledger when useful, a compact final
  validation report, and synchronized README/status-table text.
- Confirm the paper root module imports the post-paper audit ledger and that the
  audit ledger has one source-numbered theorem alias or wrapper for each final
  named endpoint.
- During final export curation, audit every broad paper module re-export as
  well as `PaperInterface.lean`. A completed paper can still look conditional
  to downstream users if `MainTheorems.lean` re-exports old proof-adapter
  models, coupled-outcome variants, or source-bridge staging theorems as part
  of the paper surface. Keep those declarations in the reusable library or
  audit ledger when useful, but expose the source-shaped final theorem in the
  paper module and status artifacts.
- Do a full DAG finalization pass before handoff:
  - Cross-check the DAG against the source paper and `PaperInterface.lean`.
    Add missing paper-facing definition/lemma/proposition/theorem/corollary or
    appendix-remark boxes, and remove implementation-only boxes unless they are
    the exact remaining caveat or a documented paper-facing bridge.
  - Re-read every node as human prose. Green/formalized nodes should summarize
    the paper claim, not how the Lean proof was implemented. Caveat or
    conditional nodes should name the exact remaining semantic issue.
    A reviewer should be able to understand the mathematical result from the
    green box itself without recognizing any paper-internal TeX label or Lean
    declaration name.
    Do not write status words such as "closed", "proved", "formalized", or
    "verified" inside green node bodies; the node color/style already carries
    that information. Likewise, avoid vague "open" text in partial/conditional
    nodes: name the missing theorem, model construction, or library ingredient
    needed to finish the paper result.
  - Do not split one source-numbered proposition/theorem/corollary into
    multiple green boxes merely because the Lean proof has formula, finite,
    certificate, or boundary helper layers. Use one green paper-facing node for
    the source result, with its paper number and a short statement of the
    actual mathematical conclusion. Make helper layers yellow/model nodes only
    when they are needed to explain real dependencies, and never duplicate the
    same numbered result across helper, formula, and final-result green boxes.
  - Before accepting a rendered DAG, run a label/duplication audit: grep the
    TeX for source labels and Lean names such as `thm:`, `lem:`, `source_`,
    and long declaration fragments; count occurrences of each numbered
    result header; and visually confirm every green result node states the
    paper-facing conclusion rather than the implementation route.
    Run this DAG audit as part of the post-formalization closeout command path.
    Do not wait for a human to ask whether the DAG and validation report satisfy
    the workflow; if the paper is being claimed complete or public-ready, the
    DAG, rendered PDF, status rows, and final report must already have passed
    this paper-facing audit.
  - Use the shared DAG template's node-type styles, not just status color:
    `dag_model` for definitions/model layers, `dag_lemma` for lemmas/supporting
    lemma clusters, and `dag_result` for theorems, propositions, corollaries,
    and final paper-facing results. Keep the legend consistent with the styles
    actually used in the diagram.
  - Check edge semantics. Solid arrows are Lean-checked dependencies; dashed
    arrows are caveats, bypassed paper routes, or non-required context. Remove
    redundant arrows if they make the diagram harder to inspect.
  - Render from the paper folder and visually inspect the PDF or a PNG
    conversion. Fix overlap between boxes, legends, labels, metadata, and
    arrows; preserve visible whitespace between neighboring nodes and clear
    routing lanes between columns.
- Run `python3 scripts/audit_repository.py --paper <paper-folder> --paper-closeout --include-active --info-limit 0`
  after post-paper cleanup and after every report/DAG closeout edit, but only
  once the paper is at a real closeout/publication boundary or the user has
  explicitly requested post-validation. Do not run this command just because an
  unfinished paper reached a clean compile point; use targeted builds,
  placeholder scans, and row-scoped judge checks for active formalization work.
  Treat its
  PaperInterface/PostPaperAudit and
  DAG/report closeout findings as part of the final audit: no tuple witness
  interfaces, no standalone proof-facing formula aliases in the audit ledger,
  no stale `Lean witness` report language, no completed-paper status rows that
  hide caveats in prose, and no missing/stale DAG audit, final validation
  report, rendered DAG PDF, or visual-inspection evidence.
  Also run the unfiltered `python3 scripts/audit_repository.py` before broad
  repository handoff when you need global hygiene, but the paper-specific
  targeted command is the mandatory post-formalization gate for the paper being
  closed. If the unfiltered audit reports findings from other papers, record
  them separately; do not downgrade or delay a paper whose `--paper-closeout`
  audit and paper-local validation gates pass.
  Do not use this global audit as an excuse to rerun LLM-as-judge workflows for
  every paper. It may check tracked sidecar freshness and report stale/missing
  evidence, but judge reruns should stay scoped to the paper being closed unless
  the user explicitly asks for an all-paper refresh.
  Also run `python3 scripts/audit_repository.py --library-only --library-premise-audit` when a
  completed paper uses recently added or extracted library APIs. Informational
  library certificate findings are not errors by themselves, but any completed
  paper wrapper that still exposes one of those certificate/source-boundary
  parameters must either construct it internally, route it through validated
  paper assumptions, or be downgraded to partial/conditional.
  Keep the paper validation report paper-local: record audit findings that
  affect the paper being reported, but do not put unrelated global repository
  errors or other active-paper warnings into that paper's validation report.
  Mention unrelated global audit failures in the agent final/status message or
  a separate repository-maintenance note instead.
- Update the paper-local `status.json` at the same time as the DAG and final
  report, using the exact caveats from the final report. Then
  run `python3 scripts/sync_paper_status.py` so the generated top-level
  `README.md` status block, `docs/PAPER_STATUS.md`, `papers/status.json`,
  `papers/human_status.json`, and `site/index.html` status table all move
  together. Do not manually edit generated table rows, and do not let any public
  status surface keep stale "partial" or "active" wording after a paper-local
  validation report says a paper is formalized.
- Use one status vocabulary per artifact. At paper and repository level,
  `formalized` is the status for a paper/result whose Lean statement and proof
  compile with its caveats documented. Lean verification is the mechanism, not a
  separate status category. Do not use `Verified in Lean`, `Verified`, or
  `Verified with caveat` as paper-status labels, and do not title a status
  section `verification status`; use `Formalized`, `Formalized with caveat`,
  `Partially formalized`, or the paper-local lowercase equivalents from
  `docs/STATUS.md`.
- For source-version differences, make the primary paper target explicit and
  describe later-version wording as a refinement or correction to a specific
  result. Avoid blended labels such as `conference/journal` when they obscure
  the target, and avoid process jargon such as `crosswalk` in public-facing
  reports; say directly that the folder formalizes the source paper, with the
  named theorem checked against the refined wording from the later version.
- **CRITICAL MANDATE: Never lie by omission.** Your validation report MUST list all major theorems, propositions, and sections from the paper. If a result or section was deferred, skipped, or is otherwise unformalized, you MUST list it in the report, mark its status as `not formalized`, and explain why it was deferred. Always be honest and complete regarding the paper's contents.
- The report must first present the paper interface: the definitions and
  formatted mathematical objects the reader needs to inspect, even when the
  source did not number them as "Definition." Examples include bias, aggregate
  posterior, calibration, objective functions, equilibrium notions, allocation
  rules, or any paper-specific named/boxed notation. Give each definition in
  paper notation plus its single main reader-facing Lean declaration, preferably
  from `PaperInterface.lean`.
- Then state each named theorem/proposition/corollary once, matching the paper
  text at theorem-box granularity. Do not expand one source theorem into dozens
  of auxiliary lemmas in the human report. Put only one direct Lean interface
  statement declaration under each paper-facing result, ideally from
  `PaperInterface.lean`. If a source theorem has separately numbered clauses,
  list each clause as its own paper-facing result with one declaration. Keep
  auxiliary implementation inventories in the Lean audit ledger, README, or
  proof files.
- The report must summarize: source version checked, named-result completion
  status (including unformalized items), additional assumptions introduced
  beyond the paper, proof-strategy deviations from the paper, and any suspected
  paper errors or inconsistencies found during formalization.
- Keep Lean declaration inventories out of the final report except for the
  single direct paper-interface declaration needed to identify each source
  result. Do not put comma-separated helper declarations, source declaration
  lists, theorem aliases, or proof-seam inventories in final-report status
  tables. Put helper theorem ledgers, alias lists, and proof-seam inventories in
  `PostPaperAudit.lean`, the README theorem ledger, or `SOURCE_AUDIT.md`.
- If the final report starts reading like an implementation ledger, split it:
  keep the report as a short human assessment of the source claims, proof
  deviations, findings, reusable lessons, DAG, and validation checks; move
  source-line mappings to `SOURCE_AUDIT.md` and declaration inventories to
  `PostPaperAudit.lean` or the README.
- Distinguish agent audit from human review. A report may say an agent
  source-audited every row, but it must not say rows were "reviewed" or imply
  dashboard completion unless a human actually saved those dashboard reviews.
- If no extra assumptions, deviations, or caveats were needed/found, state that
  explicitly in the report rather than leaving sections implicit.
- Keep the report human-facing. Do not include routine shell commands such as
  `rg -n ...` scans or full build command blocks unless the exact invocation is
  essential to understanding a caveat. Summarize validation/build checks in prose
  instead. If the report is getting long because it lists every helper theorem,
  stop and replace that section by a short paper-definition/theorem interface
  plus one main declaration name for each paper-facing theorem or definition.
- The report should read top-down for a researcher who cares about the paper,
  not Lean. Put the human verdict, closeout status, source/scope, a short
  researcher summary of checked results, remaining mathematical boundaries,
  extra assumptions, proof-strategy deviations, reusable proof ideas, and paper
  issues/caveats before any proof ledger. Put validation evidence, audit
  commands, row counts, generated ledgers, declaration inventories, and proof
  plumbing near the end. Do not place hidden-premise audit blocks, command
  transcripts, validator ledgers, or long Lean-centered proof inventories
  before `Detailed Formalization Evidence`.
- Do not paste standalone generated-audit prose into the final validation
  report. In particular, do not add a generated-audit front-matter section or
  dated generated-audit blockquotes. If the result matters to the reader,
  summarize it once in ordinary language under `Validation Checks` or
  `Paper Assumption Provenance`.
- Do not title the front proof summary `What Has Been Proven`. In practice that
  heading invites long implementation ledgers. Use `Researcher Summary of
  Checked Results` for the short paper-facing summary and
  `Detailed Formalization Evidence` later for Lean/provenance detail.
- Avoid repetition. Do not include both a long top verdict and a long final
  verdict saying the same thing. Put a short `Completion status: ...` line in
  `Closeout Status` immediately after `Human Verdict`, and keep the explanation
  in `Human Verdict`.
- The `Human Verdict` section must be a two-to-four sentence executive summary
  for a non-Lean reader. It should state the formalization status, the main
  remaining mathematical/library boundary if any, whether a paper-correctness
  issue is being claimed, and whether human dashboard sign-off exists. Do not
  put Lean declaration names, validator row counts, audit digests, source-record
  inventories, command outputs, proof adapter names, or Lean footprint numbers
  in this section; put those details in the later source, assumption, DAG,
  statement-validator, and validation-command sections.
- The `Proof-Strategy Deviations` section is only for human-facing
  mathematical departures from the paper's proof route or theorem statement.
  Do not list source-record packages, deterministic certificate plumbing, proof
  adapter names, declaration inventories, audit architecture, dashboard parser
  changes, or other Lean implementation route notes there. If the only
  differences are explicit formalization boundaries, say `None beyond the
  formalization boundaries already recorded above` and point to the assumptions
  or remaining-gaps sections.
- Put likely source typos, missing constants, sign-convention inconsistencies,
  source-version corrections, and theorem-statement repairs in `Mathematical
  Typos or Other Fixes Suggested in the Source Paper`. Write these as short
  human-facing mathematical notes and avoid Lean declaration names. When the
  evidence is only a formalization caveat, say that directly instead of claiming
  the paper is wrong.
- Use `Paper Issues or Caveats` for the status-facing conclusion after those
  source-fix notes: for example, whether the paper has a real caveat, whether a
  source-quality note is nonblocking, or whether no paper-level caveat is being
  claimed. Include the section even when the body is `None found.`.
- Avoid wide Markdown tables for definition inventories when the notation or
  declaration names are long. Use a concise bullet checklist instead, with the
  paper notation first and the Lean interface declaration second.

Use this report template (create in the paper folder, for example
`FINAL_VALIDATION_REPORT.md`):

```markdown
# Final Validation Report: <Paper Short Name>

## 1. Human Verdict
<Two-to-four plain-language sentences. State the current formalization status,
the main remaining mathematical/library boundary if any, whether a
paper-correctness issue is being claimed, and whether human dashboard sign-off
exists. Do not include Lean declaration names, validator counts, audit digests,
source-record inventories, command outputs, or Lean footprint numbers here.>

## 2. Closeout Status
- Completion status: <formalized / formalized with caveat / partially formalized / not formalized>
- One-sentence recap: <do not repeat the whole human verdict>

## 3. Source and Scope
- Paper: <title>
- Source version: <arXiv/publisher URL + version/date>
- Lean folder: <folder path>
- Human-facing theorem file: <file path>
- DAG artifacts: <tikz file>, <rendered image>
- Lean footprint: <total paper-local Lean LOC>, <PaperInterface LOC>, <review rows>

## 4. Researcher Summary of Checked Results
Summarize the checked paper definitions and named results in 3-6 concise
paper-language bullets. This is for a researcher skimming the report; do not
list Lean helper lemmas, declaration inventories, validator row counts, or
source-record packages here.

## 5. Remaining Boundaries and Gaps
- `<paper item>`: <exact remaining mathematical/library boundary in paper
  language, with the formal assumption name only if needed>
- If none: `None`

## 6. Additional Assumptions Beyond Paper
- `<assumption declaration>`: <why needed, where used>
- If none: `None`

## 7. Proof-Strategy Deviations
- `<paper result>`: <human-facing mathematical departure from the paper proof
  route or theorem statement, and why>
- Do not list Lean architecture, source-record packages, certificate plumbing,
  parser/audit changes, or declaration names here.
- If only explicit assumptions or remaining proof boundaries differ from full
  formalization, write `None beyond the formalization boundaries already
  recorded above` and refer to the assumptions/gaps sections.
- If none: `None`

## 8. Proof Tricks Worth Reusing
- <modeling/proof/library-seam lesson that should inform future papers>
- If none: `None`

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
- `<location in paper>`: <likely typo, missing constant, sign issue,
  source-version correction, or theorem-statement repair suggested by the
  formalization>
- If none: `None found.`

## 10. Paper Issues or Caveats
- `<location in paper>`: <issue description + formalization evidence in
  paper language>
- If none: `None found.`

## 11. Detailed Formalization Evidence
Record the detailed proof inventory here after the researcher-facing summary,
gaps, and caveats. Lean declaration names are allowed here when they are useful
evidence, but keep the paper result or formula first.

## 12. Paper Assumption Provenance
Every paper-facing theorem premise that is not derived in Lean should appear as
a named assumption declaration in `Assumptions.lean`, be listed in `status.json`
`review_surface.assumption_names`, and be checked in `assumption_match_llm.json`
as a true paper/source model assumption.

The source-assumption judge must work at premise granularity. A grouped
assumption declaration may summarize a family of conditions, but it does not
validate the individual `-- audit-premise:` comments under that declaration.
Every exact premise must have a `premise_judgments` entry in
`assumption_match_llm.json` with a source location and one of these meanings:
`source_text_model_primitive` / `source_text` / `paper_condition` for textually
stated model or theorem conditions, `derived_from_source_primitives` only when a
Lean derivation from source primitives already exists,
`documented_additional_assumption` for a human-approved non-caveat added
condition, `documented_caveat` for an acknowledged source mismatch, or
`partial_boundary` for a visible premise that is not yet source-matched or
derived. A paper with any `partial_boundary` premise is not fully formalized;
update `status.json`, the final validation report, and the generated status
tables accordingly. A grouped assumption declaration may also have top-level
`judgment: "partial_boundary"` when the whole declaration is a known
external/library/analytic boundary. Do not use `documented_caveat` for that
case unless the paper statement itself needs a repair.
When a theorem closes only after assuming a rich source-model record, selector
convention, argmax witness, or local-support witness, treat that record as a
boundary unless there is a separate reviewed Lean theorem deriving the record
fields from the paper's primitive assumptions. This matters for continuum
formalizations: a C.4-style positive-support witness model, an `S*`
compact/continuous optimizer package, or an Appendix-B common-floor selector
package can be scientifically useful, but the full paper remains partial until
those packages are derived or explicitly accepted as source assumptions.
For continuum selector and positive-support work, source-facing premise
reductions are useful but not closure. A finite-vector `S*` objective wrapper
reduces an opaque range-dependence premise, a global floor-tracking wrapper
reduces a dyadic selector-envelope premise, and a positive-support `_fields`
wrapper reduces a record-construction premise; none of these derives the
paper's arbitrary optimal selector, concrete weighted objective continuity,
finite-level source realization equality, or non-finite-range witness from
primitive global paper assumptions by itself.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper assumptions recorded. |

## 12. Displayed Formula Provenance
Every displayed or source-defining formula used by a named result should have
an exact paper-facing row or exact subclaim row. Broad aggregate rows are not
enough for full validation. Formula rows are closed only when the formula is
derived in Lean from source primitives or from separately validated paper
assumptions.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No displayed formulas checked. |

## 13. Library Lift Pass
- <paper-local component>: <target EconCSLib module and extraction status>
- If none: `None`

## 14. DAG Audit
- Rendered artifact: <yes/no, visual inspection method>
- Topology: <missing/extra boxes fixed or none>
- Layout: <overlap/routing status>

## 15. Validation Checks
- <build/audit/DAG/no-placeholder outcomes in prose>
- Machine-required closeout evidence may include the exact targeted repository
  audit command here, but keep commands out of the executive verdict and proof
  narrative.

## 16. Paper Definitions Checked
These are the mathematical objects from the paper interface. All should be
exposed in `PaperInterface.lean`.

- <Paper object>: <paper notation and one-line statement>.
  Lean: `<PaperInterface.definitionName>`.
- <Next paper object>: <paper notation and one-line statement>.
  Lean: `<PaperInterface.definitionName>`.

## 17. Named Theorem Statements Checked
### Theorem <n>
**Paper statement.** <one theorem-box-level statement matching the source>

**Lean interface statement.**
- `<PaperInterface.theoremN_part>`: <which paper clause it states>

**Status.** <formalized / conditional / not formalized>. <1-4 lines of caveats only if needed.>

## 18. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Generate it from the
validator ledger rather than from memory.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| <paper item label> | `<PaperInterface.declaration>` | <human/model/agent validators, judgments, dates, stale flags> | <validator comments or `None`> |

```

## Component 2: Proof Reference Routing

Do not load one giant theorem-proving playbook. When starting a nontrivial Lean
proof, read only the reference for the library layer being touched; if the proof
crosses layers, read at most the generic foundation reference and one domain
reference.

| Touched code | Read |
|---|---|
| `EconCSLib/Foundations/Math/*`, graph/counting/rounding/sign lemmas | `references/proof-foundations-math.md` |
| `EconCSLib/Foundations/Probability/*`, finite PMFs, Markov kernels/chains, CTMCs, renewal-reward, reward-rate, concentration, measure inequalities, continuous densities, RUM/noise laws, order statistics, large deviations | `references/proof-foundations-probability.md` |
| `EconCSLib/Foundations/Optimization/*`, argmax/existence/objective wrappers | `references/proof-foundations-optimization.md` |
| `EconCSLib/Applications/RecommenderSystems/*`, accuracy/diversity, producer fairness, count allocation | `references/proof-recommender-systems.md` |
| `EconCSLib/Algorithms/Online/*`, online allocation/matching, regret/Yao | `references/proof-algorithms-online.md` |
| `EconCSLib/MechanismDesign/Auctions/*`, digital goods, GSP, combinatorial auctions | `references/proof-mechanism-design.md` |
| `EconCSLib/Markets/*` or `EconCSLib/SocialChoice/*`, matching, fair division, rankings, social choice | `references/proof-markets-social-choice.md` |

`references/proof-strategies.md` is only a short router/index for these files.
Do not load detailed proof references for routine README/DAG/status edits or
simple wrapper repairs.
When updating this skill from a proof session, put proof tactics and theorem
patterns in the relevant `references/proof-*.md` file. Keep `SKILL.md` limited
to workflow, routing, folder contracts, validation, and context/source-control
rules. Before committing a skill update, run a quick grep for paper IDs, named
theorem numbers, and declaration names in `SKILL.md`; any substantive match
should usually be moved to a reference file. Acceptable matches are routing
pointers, examples in folder-contract text, and generic validation templates.
