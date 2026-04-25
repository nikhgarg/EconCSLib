---
name: econcs-formalizer
description: Formalize economics-and-computation papers in Lean. Use when asked to add, continue, triage, or plan Lean formalizations of EC/ACM EC/SIGecom-style papers; extract reusable finite/discrete primitives; choose theorem seams; repair Lean/mathlib proof scripts; or prepare general handoff guidance for future formalization work.
---

# EconCS Formalizer

Use this skill to turn economics-and-computation papers into maintainable Lean
code. Keep repository-specific status out of this file; in `EconCSLib`, that
belongs in `docs/ECONCSLEAN_CURRENT_STATUS.md`.

## Component 1: Workflow and Organization

### 1.1 Core Rule

Formalize theorem seams, not PDFs. Start from the paper's precise definitions,
the main result to be checked, and the smallest reusable lemmas needed to close
that result.

Follow the original paper's proof structure as closely as is practical. Preserve
named definitions, lemmas, propositions, and theorem numbers in Lean declaration
names, docstrings, and README status rows. When deviating from the paper proof
because Lean needs a reusable intermediate lemma or a cleaner finite/discrete
interface, make the deviation explicit and keep the paper-facing wrapper close
to the original named result.

### 1.2 Library Layering Rule: Textbook vs. Audit Trail

Think of the repository as having two distinct roles: **`EconCSLib` is the textbook. The `papers/` directory is the audit trail.**

- **`EconCSLib/` (The Textbook):** Put generic, abstracted EC/CS/econ results here. If a definition, algorithm, or theorem is foundational enough that a graduate student should know it, or if a second paper might build on it (e.g., Gale-Shapley, Nash equilibrium, LP duality), it belongs in the core library.
  - **Abstraction:** Code here should be highly abstracted and stripped of paper-specific notation. Use generic types (`α`, `β`) and naming conventions consistent with `Mathlib`.
  - **Ownership:** Main library modules own reusable primitives: allocations, valuations, mechanisms, rankings, PMFs, finite expectations, graph/path lemmas, and generic algorithm correctness patterns.

- **`papers/` (The Audit Trail):** Each paper-specific folder is a formalization artifact proving that the specific claims in a specific PDF are true.
  - **Notation Fidelity:** Translate paper-specific notation (e.g., exactly matching the paper's index variables like `u`, `j`, `t`) into the shared primitives.
  - **Paper-Facing Wrappers:** Write theorems whose signatures match the paper *exactly*. These should be thin wrappers that call the generic library theorems. (e.g., `theorem roth82_theorem_1 : ... := EconCSLib.Markets.Matching.da_is_stable`).
  - **Local Ledger:** Keep the paper's specific narrative flow in `MainTheorems.lean`, `README.md`, and `DependencyDAG.tex`.
  - **Upstreaming Workflow:** It is normal to build everything inside a `papers/` folder initially. Once a proof is stable, **upstream** the generalized math into `EconCSLib`, leaving only the thin wrappers and paper-specific stepping stones behind.

- **Standard for Upstreaming:** To prevent "upstream bloat," use the "Second Paper" test: **Only move a result to `EconCSLib` if a second paper would likely need it.** Foundationally reusable math (like Gale-Shapley, Nash equilibrium, or LP duality) passes this test; hyper-specific algebraic lemmas or messy intermediate steps used only for one paper's specific narrative should remain in that paper's folder.
- If two papers could use a lemma after renaming variables, it belongs in the generic library.
- If a proof starts with a paper-local lemma and it becomes generic, extract it before building more paper-specific code on top of it.

### 1.3 Paper Folder Contract

Each paper-specific folder should be auditable by a human who wants to compare
the Lean statements against the paper.

- **Required Template Structure:** Every paper folder must strictly follow the `papers/TEMPLATE/` format. This includes:
  1. A `README.md` (see details below).
  2. A `DependencyDAG.tex` providing the proof roadmap.
  3. A `MainTheorems.lean` file holding the paper-facing wrappers.
  4. A local `.gitignore` file.
- **Local Gitignores:** Every paper folder *must* contain its own `.gitignore` that explicitly ignores `*.pdf`, `*.aux`, `*.log`, `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`. **The overall repo `.gitignore` should not contain paper-specific exclusions.**
- **Reproducible PDF:** A copy of the source PDF must be downloaded and kept in the local paper folder so humans and agents can read exactly what is being reproduced. Because of the local `.gitignore`, this PDF will not be committed to Git, preventing repository bloat. Work from this local file; do not repeatedly search the web for it.
- **README Requirements:** The `README.md` must clearly identify the exact
  source version of the paper (e.g., arXiv version `vX`, conference year) and provide URLs.
- Add one central Lean file for paper-facing theorem statements, conventionally
  named `MainTheorems.lean`, `PaperTheorems.lean`, or the existing paper root if
  the folder already has a root module. This file should state and prove only
  the main theorem wrappers and import the detailed proof files.
- Main theorem definitions/functions in that central file should mirror the
  paper statement closely enough that a human can inspect just this file and
  verify the intended theorem was formalized. Use paper theorem numbers/names in
  docstrings and keep wrappers thin.
- For large campaigns, add one adjacent Lean declaration ledger file (for
  example `PaperFacingTheorems.lean`) that is the single-file human verification
  target for the folder’s claims.
  The file should be declaration-ordered by paper section and should expose the
  paper-facing definitions and full theorem statements (with assumptions and
  short paper-context comments) rather than `#check` entries alone.
- **CRITICAL MANDATE - NO HIDDEN DEFINITIONS:** A human reviewer cannot verify a theorem if its core terms are opaque references to generic library modules (e.g., `EconCSLib.Statistics.priorWeightedVariance`). The ledger file MUST expose the exact mathematical formulas for the paper's definitions. Do this by defining paper-specific `abbrev`s or `def`s at the top of the ledger that spell out the raw formulas exactly as they appear in the paper, and then use those local definitions in your paper-facing theorem statements (or prove they equal the generic terms). A reviewer must see the actual math equations inside this single file without needing to open imported generic modules.
  Include for each entry:
  1. the declaration name,
  2. a compact paper-style statement in comments,
  3. the key assumptions,
  4. and source location when a declaration is not a plain wrapper.
  A completed index should show the full paper-facing sequence and the final
  paper-level theorem explicitly.
- Add a structured folder `README.md` theorem-status table with columns like:
  paper theorem/definition, Lean declaration, status (`formalized`,
  `conditional`, `scaffold`, `not started`), file, and remaining assumptions.
- **Paper Directory and Namespace Convention:** All new paper folders, modules, and internal namespaces MUST be named using the format `[AuthorInitials][2DigitYear][Descriptor]` in PascalCase (e.g., `MSVV07AdWords`, `LMMS04FairDivision`, `KR21Monoculture`). This guarantees collision-proof Lean namespaces while immediately communicating the citation. All paper implementations sit within the `papers/` directory.
- **Initial Proof Roadmap (Dependency DAG):** At the *very beginning* of formalizing a new paper, before writing any deep proof code, you must create a comprehensive proof roadmap. Read through the paper carefully to identify *every* named result (Definitions, Lemmas, Propositions, Theorems, Corollaries) and map out exactly how they relate to each other. Encode this roadmap as a dependency DAG in a TikZ source file (with a rendered image) in the paper folder. This ensures no named result is overlooked, helps you understand the overall proof architecture, and gives humans a clear audit of the theorem flow.
  - **Project pattern in this repo:** for Monoculture, keep the active artifact at
    `papers/KR21Monoculture/DependencyDAG.tex` and a rendered image alongside it.
  - All paper DAGs MUST `\input` the shared preamble located at `docs/tikz/dag_preamble.tex`.
  - Use the exact node styles defined in the preamble: `dag_result` (green), `dag_lemma` (yellow rounded), `dag_model` (blue ellipse), `dag_unformalized` (dashed gray), `dag_conditional` (orange rounded), and `dag_caveat` (red diamond).
- **DAG Formatting and Clarity Mandates:**
  - The DAG must encode formalization status and node type explicitly by using the preamble styles.
  - **Node Content:** Node text MUST begin with a bolded header indicating the Theorem/Lemma/Definition name and, if available, its location in the paper (e.g., `\textbf{Theorem 1 (Section 4)} \\ Description` or `\textbf{Lemma 12 (App. E)} \\ Symmetry reduction`). Provide a brief, readable description on the following line(s).
  - **Legend:** You MUST include a Legend using the shared helper macro from the preamble, e.g., `\daglegend{(legRes)(legLem)(legDef)(legOpen)}{Legend}`. Place legend nodes concisely at the top.
  - **Edge Routing (No Overlaps):** Use explicit positioning (`node distance`, `below=of`, `right=of`, `xshift`, `yshift`) carefully. **Prefer straight paths or simple orthogonal routing (`|-`, `-|`) whenever possible without overlap.** Use wide horizontal spacing (standardized at `4cm` in the preamble) and a column-based layout to ensure paths are clear. Only use complex curves (`to[out=..., in=...]`) or bends when necessary to route around an immediate obstacle. Use `dag_arrow` and `dag_dashed_arrow` from the preamble for styling.
- Keep the DAG updated after every major paper update (for example: a named
  paper theorem/lemma closed, a dependency refactor that changes proof flow, or
  a status transition between scaffold/conditional/formalized).
- If a theorem is only conditional, the README must name the exact certificate
  or assumption declaration that remains. Do not describe it vaguely as
  "technical details".
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
  together in the working tree.
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
- Use targeted `rg` searches for the strongest paper-facing wrapper, the exact
  remaining certificate/assumption named in the README, and the internal lemma
  that feeds it. Avoid scanning broad proof files or docs until those anchors are
  identified.
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
- Before editing, state the one active seam in local notes or the handoff doc:
  public theorem wrapper, internal lemma/certificate being attacked, exact
  remaining assumption, and the build command that validates the slice.
- Do not revisit closed layers first. Search for the strongest current endpoint
  and the precise "remaining" text, then work on that next bridge. In this repo,
  paper README rows and `docs/ECONCSLEAN_CURRENT_STATUS.md` should say which
  algebra, symmetry, probability, or model-integration layers are already closed.
- When stopping or moving papers, document "do not redo" information: closed
  theorem layers, the current endpoint, the next bridge, known traps, and the
  last passing build command. This prevents future agents from spending tokens
  re-deriving the same orientation.

### 1.5 Workflow

1. Orient before editing.
   Read the repo README, roadmap, architecture notes, and paper-specific
   handoff documents. Identify the public theorem target and the smallest local
   lemma that moves it forward.
   For a brand-new paper, your *very first task* is to read through the paper to extract the proof roadmap. Produce the comprehensive named-result dependency DAG (capturing every definition, lemma, proposition, theorem, and corollary and their exact relationships) as a TikZ diagram using the shared preamble. This serves as your master plan to understand the paper's architecture. Keep it current through the campaign as results change status.

2. Context Efficiency vs. Edit Accuracy (File Reading Strategy).
   Do not over-optimize context limits by reading tiny chunks of files (e.g., using `sed` to read 15-20 lines) if you are about to use the `replace` tool. Micro-reading frequently drops necessary surrounding whitespace or context, causing the `replace` tool to fail repeatedly with "0 occurrences found". The cost of spinning in a multi-turn failure loop is far higher than the cost of reading the entire file once. Use `read_file` to ingest small-to-medium files completely, or use `grep -C 20` to get substantial context, ensuring you capture exact, copy-pasteable blocks for your `old_string`.

3. Stabilize the build first.
   Run targeted `lake build <module>` commands before making broad changes. Fix
   dependency, import, or cache problems before interpreting downstream proof
   errors.

3. Choose finite/discrete models first.
   EC papers often have useful finite entry points: finite agents, items,
   actions, rankings, allocations, mechanisms, PMFs, and finite sums. Formalize
   those before attempting asymptotic, measure-theoretic, or complexity-heavy
   layers.

4. Extract shared primitives into the main library.
   Reusable finite expectations, policies, allocations, valuations, mechanisms,
   rankings, conditional expectations, graph lemmas, and sign lemmas should live
   in main library modules, not buried in one paper folder. Keep only
   paper-specific definitions and wrappers in paper namespaces.

5. Make every paper pay library rent.
   When a proof needs a reusable object, add the general version once and reuse
   it. Avoid parallel versions of allocations, randomized policies, mechanisms,
   expectations, graph reachability, or inequality certificates in each paper
   folder.

6. Prefer compileable partial progress.
   If the full main theorem is not ready, add definitions, local invariants,
   certificate structures, and conditional theorems that compile. Avoid `sorry`
   unless the user explicitly asks for placeholder theorem statements.
   If Lean exposes that a paper lemma is false as stated, do not silently weaken
   the paper-facing declaration to make progress. State the paper version, prove
   the strongest true nearby lemma separately, and add a small compiled
   counterexample theorem when possible. Mark the README/status row as a
   validation issue with the exact failed hypothesis or inequality.

7. Document exact theorem seams.
   When stopping mid-proof, record the module, theorem, assumptions still
   missing, commands run, the next lemma to prove, and any closed layers that
   should not be revisited. Future agents should not have to rediscover the
   proof state.

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
- Always scope your git operations (e.g., `git checkout <specific_file>`, `git restore <specific_file>`) strictly to the files you are actively modifying.

- Lake reuses `.olean` artifacts when sources, imports, Lean version, and
  dependency artifacts are unchanged.
- After changing `lean-toolchain`, `lakefile.toml`, or dependency revisions,
  expect substantial rebuilds.
- If generated artifacts produce invalid headers or impossible import errors,
  clean generated dependency outputs and rebuild rather than patching random
  downstream files.
- If a long build is interrupted, already-finished modules usually remain
  cached; rerunning resumes from remaining work.
- Do not infer that downstream files are broken until the direct imported module
  builds.
- Existing warnings are not build failures unless the user asks for lint cleanup
  or the project enforces warning-free builds.
- If build logs are dominated by repeated non-actionable linter warnings,
  quiet only those specific style/noise linters in `lakefile.toml` (e.g., `weak.linter.style.whitespace = false`); do not
  disable proof checking or hide theorem errors.
- To save context during iteration, redirect targeted builds to a temporary log
  and print only the tail on failure or completion, e.g.:

```bash
lake build UserItemFairness.MainTheorems >/tmp/econcs-build.log 2>&1
status=$?
tail -80 /tmp/econcs-build.log
exit $status
```

- Prefer `lake build <touched-root-module>` over full `lake build` until the
  paper slice is ready for integration.

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

### 1.10 Token Efficiency and Mathlib Discovery

**CRITICAL MANDATE - DO NOT GUESS MATHLIB LEMMAS:**
When you need a Mathlib lemma (e.g., for `Filter.Tendsto`, `Finset.sum`, or topological limits), **DO NOT guess its exact camelCase or snake_case name in a loop.** This wastes massive amounts of tokens and context window.
Instead:
1. Create a minimal `/tmp/test.lean` file.
2. State the exact theorem you want to prove.
3. Use the `exact?` or `apply?` tactics inside the proof.
4. Run `lake env lean /tmp/test.lean` to let Lean's internal search engine give you the exact lemma name.
5. If `exact?` fails, search the local `.lake/packages/mathlib` repository using `grep` or `rg` for keywords, or use `Moogle` / LeanSearchClient if configured.

Never enter a cycle of modifying a single line in a shell command just to test slightly different lemma names. Stop, use `exact?`, and proceed efficiently.

Before declaring a paper "done," run a final human-facing validation pass:

- Re-read the paper-facing theorem ledger file (for example,
  `PaperFacingTheorems.lean` or the named human-facing theorem file) and check
  each named definition/theorem/corollary against the paper statement.
- Confirm every final paper-facing declaration is fully formalized with no
  hidden placeholders; no unresolved `sorry`, scaffold wrappers, or unnamed
  gaps should remain in the claimed result chain.
- If a result remains conditional, ensure assumptions/certificates are explicit
  in both the theorem statement and the paper README status table, with exact
  declaration names and no vague wording.
- Produce a final human-facing report in the paper folder alongside the DAG
  artifacts (TikZ source and rendered image). 
- **CRITICAL MANDATE: Never lie by omission.** Your validation report MUST list all major theorems, propositions, and sections from the paper. If a result or section was deferred, skipped, or is otherwise unformalized, you MUST list it in the report, mark its status as `not formalized`, and explain why it was deferred. Always be honest and complete regarding the paper's contents.
- The report must summarize: source version checked, theorem-by-theorem completion status (including unformalized items), additional assumptions introduced beyond the paper, proof-strategy deviations from the paper, and any suspected paper errors or inconsistencies found during formalization.
- If no extra assumptions, deviations, or errors were needed/found, state that explicitly in the report rather than leaving sections implicit.

Use this report template (create in the paper folder, for example
`FINAL_VALIDATION_REPORT.md`):

```markdown
# Final Validation Report: <Paper Short Name>

## 1. Source and Scope
- Paper: <title>
- Source version: <arXiv/publisher URL + version/date>
- Lean folder: <folder path>
- Human-facing theorem file: <file path>
- DAG artifacts: <tikz file>, <rendered image>

## 2. Theorem-by-Theorem Validation
| Paper item | Lean declaration | Status (`fully formalized` / `conditional` / `not formalized`) | Statement match (`exact` / `minor deviation` / `major deviation`) | Notes |
|---|---|---|---|---|
| ... | ... | ... | ... | ... |

## 3. Additional Assumptions Beyond Paper
- `<assumption declaration>`: <why needed, where used>
- If none: `None`

## 4. Proof-Strategy Deviations
- `<paper result/declaration>`: <what changed in strategy and why>
- If none: `None`

## 5. Conditional Results and Remaining Gaps
- `<paper item>`: <exact remaining certificate/assumption declaration name>
- If none: `None`

## 6. Suspected Paper Errors or Inconsistencies
- `<location in paper>`: <issue description + Lean/formalization evidence>
- If none: `None`

## 7. Final Verdict
- Completion status: <complete / conditionally complete / incomplete>
- Summary: <2-5 lines>
```

## Component 2: Theorem Proving Strategies and Suggestions

### 2.0 Classify the Proof Type First

Before writing Lean for a named paper result, classify the hard part. Different
proof types need different theorem seams; mixing them usually creates huge goals
and wasted proof search.

- **Definition/interface wrappers.** Use when the paper statement is mostly a
  named predicate or equivalence of notation. Keep wrappers thin, put the paper
  wording in docstrings, and do not mark the paper theorem complete unless the
  wrapper's hypotheses are themselves proved from earlier paper assumptions.
- **Finite expectation decompositions.** Use when the paper rewrites an expected
  payoff, utility, welfare, or probability. First prove pointwise identities,
  then finite PMF/pair-PMF sum identities, then the paper-facing equivalence.
  Group by the event/fiber that appears in the paper, not by whatever makes the
  immediate `simp` goal shortest.
  For probability-delta comparisons, prove the tiny indicator inequality first
  over the finite outcome type, then lift it with a generic PMF lemma comparing
  indicator differences. This avoids brittle rewrites under dependent
  `Decidable` instances inside large PMF goals. For strict event monotonicity,
  split the larger event into the smaller event plus a residual event, then
  prove positive residual mass from a single finite atom witness.
  For two-outcome choice probabilities, first prove the complement identity
  (`wrong = 1 - correct`) and then turn `wrong < correct` into `1/2 < correct`;
  this matches paired-density proofs more closely than assuming a half-bound.
- **Denominator-cleared finite sums.** Use when probabilities or PMFs introduce
  positive normalizers. Define the unnormalized numerator, prove denominator
  positivity once, and expose both normalized and cleared positivity
  equivalences. This keeps later sign certificates independent of probability
  division noise.
- **Rank-weight monotonicity.** Use when a ranking model such as Mallows turns a
  payoff into a finite rank-weighted average. First prove the PMF/fiber
  decomposition, then convert to a pure rank-only weight formula, then prove a
  generic cleared weighted-average lemma from pairwise cross-ratio or prefix
  dominance. Do not keep unfolding PMFs once the theorem is reduced to rank
  weights; the remaining proof should mention only rank sums, positive
  denominators, and value monotonicity.
  If a deleted or conditioned rank creates piecewise weights, first prove small
  closed-form side lemmas for the below/above/self cases and a deletion-sum
  geometric identity. Then prove same-side cases by the basic power MLR lemma
  and isolate the cross-boundary case as its own factor inequality. This is
  faster and more auditable than trying to `ring` a large all-cases theorem.
- **Sign and inequality arguments.** Use certificate structures whose fields are
  exactly the nonnegativity, strict positivity, monotonicity, or comparison
  facts needed by the final theorem. Prefer sum-level certificates for
  expectation theorems; avoid adding candidatewise or termwise assumptions just
  because they make a finite-sum lemma convenient.
  For strict inequalities over piecewise-linear functions such as absolute
  values, test equality cases early with a concrete separated or boundary
  example before building a long proof. If only a weak inequality is globally
  valid, preserve the weak theorem and isolate the extra overlap/support/
  integration argument needed for strictness.
- **Bijection/fiber enumeration.** Use when a paper counts rankings,
  allocations, histories, or type fibers. Normalize the objects with explicit
  equivalences, prove weight/exponent/cardinality preservation separately, then
  lift sums through `Finset.sum_bij`. Do not combine the bijection proof with
  the final economic inequality.
- **Game/payoff bridges.** Use when the paper says a strategy is dominant or a
  welfare comparison follows from payoff inequalities. Define the paper's
  scalar functions exactly (`f`, `g`, `h`, utilities, welfare), prove algebraic
  equivalences to the existing game predicates, then prove the theorem from a
  small crossing or payoff certificate.
  When only a ranking law changes, first rewrite payoff differences as
  candidatewise probability deltas times conditional continuation values. This
  often turns a game/probability statement into the scalar inequality written in
  the paper and avoids duplicating expectation algebra in model-specific files.
  For finite conditional utilities with exactly two possible continuation
  values, prove or reuse a generic two-outcome expectation lemma
  (`E[f]=Pr[event]x+(1-Pr[event])y`) before specializing to the paper's
  notation. This removes unnecessary model-specific assumptions like named
  `u_-i` identities.
  For strict probability bounds such as `Pr[event] < 1`, avoid analytic
  reasoning when finite support is enough: prove positive mass outside the event
  and apply a generic finite PMF complement lemma.
- **Analytic/existence/crossing proofs.** Use when the paper invokes
  differentiability, continuity, limits, asymptotic optimality, or an
  intermediate-value argument. First prove the finite game/probability algebra
  conditionally from a named analytic certificate. Only then instantiate that
  certificate from topology/analysis assumptions. Keep continuity/limit imports
  local and narrow.
  For continuous RUM/noise-model proofs, split the final finite-dimensional
  payoff algebra from the density/integration arguments immediately. State the
  algebra theorem in terms of scalar probability deltas, conditional utilities,
  and ordering inequalities, then prove the density lemmas feed those scalar
  hypotheses separately. This prevents measure-theory proof search from
  blocking a purely algebraic theorem.
  Before attempting a full measure pushforward, prove deterministic real-score
  geometry such as contraction preserving pairwise order. These lemmas are small
  algebraic inequalities and can discharge the event-implication side of a
  coupling proof independently from density/Jacobian work.
  For swap or injection arguments under a density, split the work into
  pointwise region mapping and pointwise density comparison before integrating.
  The integration theorem should then consume these as named hypotheses instead
  of mixing score geometry, density algebra, and measure transport in one proof.
  In finite/discrete analogues, prove a generic equivalence/injection
  probability bound: if an equivalence maps event `A` into event `B` and target
  atoms have at least source mass, then `Pr[A] ≤ Pr[B]`. Reuse that for
  paper-specific swap maps instead of redoing finite sums.
  For strict swap arguments, strengthen the generic lemma with one source-event
  atom whose image has strictly larger mass; prove strictness with
  `Finset.sum_lt_sum`, then compare the image event to the target event by
  inclusion. This pattern cleanly turns paired-density strictness into finite
  facts like `wrong < correct` or `λ₁ < λ₂`.
  Prefer running these swap arguments on the realization/sample space when that
  is how the paper proves them. Add marginal-identification equalities back to
  the ranking law instead of forcing a swap equivalence directly on rankings.
  This mirrors continuous change-of-variables proofs and keeps the future
  measure-theory bridge local to pushforward/marginal facts.
  Do not carry one marginal-identification hypothesis per event if the sample
  law is already described by atom preimages. Prove or reuse a generic finite
  preimage bridge of the form `mass(atom b) = Pr[f = b] -> Pr[p] =
  Pr[p ∘ f]`, then derive lambda events, first-choice events, and support facts
  from that single atom-preimage law. If the law is explicitly a finite
  `PMF.map f ν`, first prove the atom-preimage law once from the PMF map or
  outer-measure API, then keep the paper theorem stated in terms of the mapped
  laws rather than extra marginal-equality premises.
  When a paper's continuous "support everywhere" premise is only needed to show
  a finite probability is not one, add a full-support finite wrapper
  (`∀ atom, 0 < mass atom`) and construct one concrete outside-event atom.
  This is clearer than carrying a hand-picked support witness through every
  paper-facing theorem. If the finite law is induced from a realization space,
  prove full support from preimage probabilities: identify each atom with the
  probability of its realization preimage and provide one positive-mass
  realization in each preimage.
  For coupling proofs, first formalize the finite probability skeleton: a common
  sample space, marginal-identification equalities, and an event implication
  proving `Pr[A] ≤ Pr[B]`. Keep the continuous map, Jacobian/pushforward, and
  event-implication geometry as separate inputs. This usually yields a named
  paper lemma checkpoint before the measure-theoretic construction is complete.
  If event implications are really order facts about realized scores, add small
  score-level predicates and prove the event map from deterministic score
  geometry plus explicit score-to-ranking interface hypotheses. This avoids
  leaving opaque assumptions like "top cannot leave top" or "`swapi` maps this
  transition region" in the paper-facing theorem when the real-order proof is
  already available.
  For pairwise ranking events after one candidate is removed, prove the
  wrong-to-correct event map from the two relevant score coordinates and a
  coordinate-swap equation before connecting it to probability mass. Keep the
  score order interface (`wrong -> s_i < s_j`, `s_j ≤ s_i -> correct`) separate
  from the mass comparison. For lambda-gap comparisons such as `λ₁ < λ₂`, do
  the same thing with the source score order and the target after-removal
  score criterion; do not leave the final theorem with an opaque event-map
  premise when a two-line score-swap lemma will expose the paper argument.
  For i.i.d. density products, first prove the two-coordinate well-ordered
  density comparison, then multiply by the unaffected coordinate using an
  explicit nonnegativity/positivity hypothesis. Do not bury the context factor
  in a larger algebraic expression; expose a small three-coordinate density
  lemma that future mass-formula rewrites can use directly. Then add a separate
  finite mass-formula bridge (`mass atom = density product`) that rewrites the
  source and swapped atoms and applies the pointwise density lemma.
  For contraction-based `swapi` mass comparisons, do not assume the raw score
  order needed by the density swap if it follows from the contracted
  middle-beats-top event. Prove the deterministic bridge first:
  contracted `x₂` beating contracted `x₁`, together with `x₁ > x₂` and
  `0 ≤ t ≤ 1`, implies raw `r₁ < r₂`; then feed that into the density
  mass-formula theorem.
  For finite noisy-ranking asymptotics, prefer a rank-weight or atom-weight
  function that is total at the limiting parameter (`q = 0`, infinite accuracy,
  degenerate noise) over reasoning directly with a PMF constructor that only
  exists for positive parameters. Prove the limiting strict payoff gap at the
  degenerate model, prove finite rank/atom averages continuous at the limit,
  then choose the concrete parameter using a small-parameter lemma such as
  `∃ θ > lower, q θ < δ`. This avoids hiding asymptotic dominance as a field.
- **Model-instantiation proofs.** Use when a theorem says a concrete model
  satisfies abstract assumptions. Preserve the abstract theorem as a thin
  wrapper, then instantiate each assumption in separate files. Do not hide
  unproved model facts as fields of the final theorem unless the README marks
  the result conditional by that exact certificate name.
  When a paper has both fixed-parameter model facts and family-level analytic
  facts, split them. First prove a family bridge that discharges the
  fixed-parameter definitions from the model theorem for every parameter pair;
  leave only the true family analytic fields (continuity, limits/asymptotics,
  monotonicity) as named obligations. Add small parameter-convention lemmas
  such as inverse-noise monotonicity instead of redoing algebra at every use.
  If a monotonicity definition has multiple cases, split those cases too:
  prove the cases that follow from existing model MLR/order lemmas immediately
  and leave only the genuinely harder removal/conditioning cases as fields.
- **Validation/reporting proofs.** Use when checking whether a paper is done.
  Rebuild the human-facing theorem file, search the paper folder for
  placeholders, compare every paper-facing theorem statement to the source, and
  state remaining conditional certificates explicitly in the validation report.

When stuck, move sideways to a smaller seam of the same type instead of jumping
to another paper theorem. For example, in a game/existence proof, finish the
payoff algebra and abstract crossing theorem before trying to prove a concrete
Mallows/RUM family satisfies the analytic assumptions.

### 2.0.1 Proof-Type Playbooks

For each named result, write down the proof type and the next artifact before
editing. Use this compact map to avoid broad proof search.

| Proof type | First Lean artifact | Validation target | Common trap |
|---|---|---|---|
| Definition/interface wrapper | paper-facing theorem with the paper statement in the docstring | wrapper imports and compiles, assumptions match prior declarations | counting a restated assumption as proved |
| Finite expectation decomposition | pointwise identity, then `pmfExp`/`pmfPairExp` sum lemma | paper equivalence without unfolding PMF internals at the wrapper | expanding PMF probabilities too early |
| Denominator-cleared finite sum | numerator definition plus denominator positivity lemma | normalized and cleared positivity equivalence | carrying division through every sign proof |
| Rank-weight monotonicity | rank-only weight definition plus cleared average comparison | model theorem uses only the rank lemma and denominator positivity | re-entering PMF/fiber algebra after rank reduction |
| Sign/inequality proof | certificate with exactly the needed nonnegative/positive fields | final strict inequality from certificate fields | strengthening assumptions to termwise positivity without documenting it |
| Bijection/fiber enumeration | equivalence/bijection plus preservation lemmas | transported finite sum by `Finset.sum_bij` or an existing relabel lemma | mixing counting and economics in one theorem |
| Game/payoff bridge | paper scalar functions and payoff certificate | strategy/welfare predicate follows by algebra | proving analytic existence before payoff semantics are settled |
| Analytic/existence/crossing | local certificate, then continuity/limit instantiation lemmas | paper theorem from the certificate; no hidden topology assumptions | using continuity to infer a one-sided crossing direction it does not imply |
| Model-instantiation | abstract theorem first, model assumptions in separate files | concrete model wrapper has no unproved model fields | hiding model facts inside a final theorem premise |
| Validation/reporting | paper-facing Lean ledger plus final validation report | build, placeholder search, theorem-by-theorem statement check | relying on commit history instead of current compiled declarations |

For assumption-heavy theorem statements, split paper definitions by the domain
where the paper actually quantifies them. Do not package multiple definitions
into one broad predicate and then use it at a boundary point where one of the
definitions is not stated. A common example is a theorem that uses Definition 2
at equal parameters and Definition 3 only for strict parameter inequality; make
the equal-parameter lemma take only the Definition 2 field, and keep the broader
paper-hypothesis predicate as a compatibility wrapper.

For finite analytic arguments, prefer elementary local interfaces before loading
heavy topology: epsilon-delta continuity for real functions, finite sums of
continuous functions, and atomwise PMF continuity implying finite-expectation
continuity. Move those lemmas into reusable library modules when another paper
could need them.

For crossing arguments, do not assume that any intermediate-value crossing has
the desired one-sided sign. If the proof needs positivity immediately to the
right, use a last-nonpositive or first-nonnegative compact-interval lemma (for
example `exists_last_nonpos_with_right_pos_on_Icc`) and state the interval sign
change explicitly.

### 2.1 External Library Reconnaissance

Before implementing substantial probability, statistics, or learning-theory
machinery from scratch, check whether existing Lean libraries already contain
the needed theorem and whether their Lean/mathlib versions are compatible.

- Statistical learning theory: `YuanheZ/lean-stat-learning-theory`
  (`SLT/*`) formalizes empirical-process infrastructure, covering numbers,
  metric entropy, sub-Gaussian processes, Gaussian concentration, Efron-Stein,
  Dudley's entropy integral, and least-squares regression bounds. Useful module
  names include `SLT.CoveringNumber`, `SLT.MetricEntropy`, `SLT.SubGaussian`,
  `SLT.Dudley`, `SLT.EfronStein`, `SLT.GaussianLipConcen`, and
  `SLT.LeastSquares.*`.
- Related probability sources referenced by that project include
  `auto-res/lean-rademacher` for Rademacher/Dudley material and
  `RemyDegenne/CLT` for characteristic-function/CLT infrastructure.
- Optimization and convex analysis: `optsuite/optlib` (`Optlib/*`) formalizes
  convex functions, subgradients, Farkas-style alternatives, weak duality, KKT
  conditions, and convergence of standard first-order optimization algorithms.
  It is the first external place to inspect before building convex-optimization
  or LP-duality infrastructure for recommendation, market, and admissions
  papers.
- Do not add one of these as a dependency blindly. First inspect
  `lean-toolchain`, `lakefile`, and `lake-manifest`; if the toolchain is behind
  the current repo, either port only the needed lemmas into a local generic
  module with attribution or isolate a compatibility branch.
- Prefer using upstream theorem names as search terms. If porting, preserve the
  conceptual interface but adapt notation/imports to the local library layer.

### 2.2 Modeling Heuristics

- Fair division: start with finite bundles, allocations, monotone valuations,
  envy, EF/EF1-style predicates, envy graphs, and local preservation lemmas.
- Auctions/mechanisms: separate reports, outcomes, allocations, payments,
  utility, truthfulness, individual rationality, revenue, and approximation or
  benchmark predicates. For auction Test-of-Time tracks, start with finite
  certificate interfaces: fixed-price benchmarks for digital goods, explicit
  position outcomes before sorted GSP mechanisms, and bundle-allocation
  feasibility before greedy combinatorial-auction algorithms.
- Matching: separate preferences, feasibility, matching, blocking pairs,
  stability, deferred acceptance, and strategic-report predicates.
- Games/learning: separate finite games, mixed distributions, payoffs,
  equilibrium predicates, regret/calibration, and empirical distributions.
- Statistical learning/probability: before building custom measure-theoretic
  probability, look for reusable concentration, sub-Gaussian, covering-number,
  entropy, empirical-process, and regression results in SLT-style libraries;
  when toolchain mismatch prevents direct import, port narrowly into generic
  EconCS probability/statistics modules.
- Online algorithms: separate histories, feasible irrevocable actions,
  objective value, benchmark/offline optimum, and competitive-ratio statements.
  For AdWords/MSVV, first close the finite offline benchmark and LP weak-duality
  layer: assignments, spend, revenue, budget feasibility, residual budget,
  feasible next-query assignment, offline optimum, fractional LP feasibility,
  integral-to-fractional embedding, dual feasibility, and dual objective. Then
  model Balance/MSVV as a history fold whose local step chooses
  a feasible advertiser maximizing the scaled bid
  `bid * (1 - exp(spentFraction - 1))`; prove run feasibility separately from
  the competitive-ratio invariant. Under small bids, prove the boundary lemma
  that a blocked advertiser has spent fraction strictly above `1 - ε`; this is
  the finite replacement for repeatedly handwaving away exhausted advertisers.
  Also expose the dual-cover proof through slack scores:
  `bid * (1 - alpha) ≤ beta` implies the LP dual constraint
  `bid ≤ bid * alpha + beta`; this is the bridge from Balance choices to
  `DualFeasible`. For finite advertiser sets, define max-slack query duals and
  normalized assignment-induced MSVV advertiser duals
  `(exp spentFraction - 1) / (exp 1 - 1)`, then prove they are dual-feasible
  before trying to prove the global scaled dual-objective bound. The key
  normalization identity is
  `(1 - 1/e) * bid * (1 - normalizedAlpha) =
  bid * (1 - exp (spentFraction - 1))`, i.e. scaled normalized slack is the
  Balance score. Package the last finite charging argument as a named
  objective-bound certificate so the paper-facing `1 - 1/e` theorem remains a
  thin wrapper.
  Before attacking the objective bound, prove run monotonicity: spend, spent
  fractions, and assignment-induced MSVV dual alphas only increase along a
  feasible online history. This yields the key comparison that final slack
  scores are bounded by earlier Balance scores. Use that comparison with the
  Balance maximizer to close the non-exhausted-query beta charge; handle
  exhausted advertisers separately with the small-bids boundary lemma by first
  proving a normalized final-alpha lower bound at spent fraction `1 - ε` and
  then a scaled normalized final-slack bound
  `bid * (1 - exp (-ε))`. For finite max-slack query duals, package the mixed
  scaled normalized query charge in a summation-friendly form: chosen Balance
  score plus an explicit max-bid small-bids error term. Then introduce
  recursive history charge sums mirroring the online fold, prove the scaled
  normalized list-summed beta bound for fresh nodup histories, and reindex from
  list sums to finite query sums only under an explicit coverage assumption such as
  `historyFinset history = Finset.univ`. In parallel, define a recursive
  revenue-increment trace for the same fold, prove final run revenue equals the
  trace from the initial state, and prove the recursive Balance charge is
  bounded by that revenue trace. For the advertiser-alpha part, use the
  normalized-dual increment identity and the finite analytic bound
  `exp x - 1 ≤ x * exp ε` for `0 ≤ x ≤ ε`; this gives a per-assignment charge
  bounded by the assigned bid plus `bid * (exp ε - 1)`. Fold that through the
  history as an explicit `historyMaxBidAlphaErrorSum` and combine it with the
  exhausted-advertiser beta error `historyMaxBidErrorSum`. Package the exact
  idealized theorem as a history-accounting certificate and the finite
  small-bids theorem as an approximate objective-bound certificate with the
  additive error
  `historyMaxBidAlphaErrorSum ε history + historyMaxBidErrorSum ε history`.
  Then combine the two error sums into `historyMsvvSmallBidsErrorSum` and prove
  the algebraic bound by `ε * (Real.exp 1 + 1) * historyMaxBidSum` for
  `0 ≤ ε ≤ 1`; under a nodup-cover history, reindex `historyMaxBidSum` to the
  finite query sum `∑ q, maxBidForQuery q` for the paper-facing statement. Add
  a delta-form wrapper saying the algorithm is competitive up to additive `δ`
  whenever that algebraic error is at most `δ`; when `historyMaxBidSum` is
  positive, also expose the explicit threshold
  `min 1 (δ / ((Real.exp 1 + 1) * historyMaxBidSum))` for the `SmallBids`
  assumption. A fixed-instance limit-style wrapper can remove the additive term
  under an arbitrarily-small-threshold assumption by a half-gap contradiction.
  For canonical finite query models, use `Query = Fin n` and
  `List.finRange n` as the history: prove a tiny helper pair
  `historyFinset_finRange` and `finRange_history_nodup`, then provide
  no-boilerplate wrappers whose additive term is stated directly as
  `ε * (Real.exp 1 + 1) * (∑ q : Fin n, maxBidForQuery q)`. This avoids making
  paper-facing theorem statements carry nodup-cover hypotheses when the
  standard finite index type already supplies them.
  For the paper's small-bids limit, do not collapse the argument to a fixed
  finite instance. State a family-level theorem over dependent query sizes
  `Fin (n k)`: if the explicit finite error is eventually below every positive
  `δ`, or if the explicit small-bids threshold eventually holds for every
  positive `δ`, then the Balance/MSVV guarantee is eventually additive-`δ`.
  Then use a reusable real-sequence lemma such as
  `Sequence.le_of_seqTendsTo_eventually_le_add` to convert eventual additive
  guarantees plus convergence of the scaled benchmark and online revenue into
  the final limiting inequality. If the paper-facing assumptions give
  convergence of the unscaled offline optimum, use a nonnegative scalar
  convergence lemma such as `Sequence.SeqTendsTo.const_mul_of_nonneg` to state
  the conclusion as `msvvRatio * optLimit ≤ revenueLimit`.
  Package the final paper-facing statement as an explicit family structure
  (`MsvvSmallBidsLimitFamily` in `EconCSLib`) rather than leaving a long list
  of hypotheses at every theorem call site.
  This is the faithful paper-level theorem for the finite-family model; do not
  force any fixed finite instance theorem to be exactly `1 - 1/e`.
  After the family theorem is closed, formalize Section 6-style variants as
  reductions to effective-bid AdWords instances. The useful transformations are
  arbitrary effective charges, click-through-rate bids (`CTR * bid`),
  advertiser-weighted bids (`weight * bid`), availability/delayed-entry masks
  that zero inactive bids, and slot-query expansion. Be explicit that the
  slot-query expansion is an independent slot-query reduction; it does not by
  itself enforce a per-page distinct-advertiser constraint unless a separate
  feasibility layer is added.
  For the Section 7 randomized lower bound, do not bury Yao's lemma inside the
  algorithm proof. First add a finite lower-bound certificate interface whose
  fields are the distributional instance family, deterministic-algorithm
  expected revenue bound, offline benchmark lower bound, and limiting ratio;
  then connect the paper's construction to that certificate.
  In `EconCSLib`, use the generic finite Yao theorem in
  `EconCSLib.Decision.Yao` for this step: prove deterministic average payoff
  under a finite input distribution, then derive the existence of a bad input
  for every randomized algorithm. Keep normalized revenue explicit so the
  offline benchmark division is visible at the paper wrapper. For the MSVV
  b-matching construction, specialize the hard input distribution to uniform
  bidder permutations (`uniformPermutationDistribution`) and leave the
  deterministic expected-revenue inequality as the named remaining field until
  the round-allocation symmetry argument is fully modeled. Name the paper's
  harmonic spend cap separately (`theorem9BidderSpendUpperBound` and
  `theorem9NormalizedRevenueUpperBound`) so the asymptotic comparison with
  `1 - 1/e` is not hidden inside a generic certificate. Also isolate the
  paper's `E[q_ij] <= 1 / (N - i + 1)` claim as a round-allocation certificate
  before proving the harmonic cap; this keeps the symmetry argument and the
  summation argument separate. If the model has realized per-instance
  allocation variables, add a pointwise allocation certificate and prove the
  finite-expectation algebra from pointwise capped spend to capped expected
  spend. Then, when the paper argues by uniform random order, add a
  symmetry/capacity certificate: ineligible positions get zero allocation, each
  round has total eligible allocation at most one, eligible positions have equal
  expected allocation, and the eligible set cardinality supplies the
  `1 / (N - i + 1)` denominator. When the symmetry comes from a uniform random
  order, prefer a pointwise relabeling certificate over assuming expected
  equality directly: prove an input-space equivalence and use uniform finite
  expectation invariance (`pmfExp_uniformPMF_eq_of_comp_equiv` /
  `uniformPermutationExpectation_eq_of_relabel`) to derive the expected
  equality. For MSVV Theorem 9 specifically, prefer the observed-prefix
  interface once available: factor allocation through `theorem9ObservedPrefix`
  and use `theorem9ObservedPrefix_mul_swap_eq` to prove that swapping two
  positions in the current suffix leaves the algorithm's information unchanged.
  If the allocation rule is already stated over actual bidder labels in the
  visible set, use the feasible observed-prefix certificate; it derives
  position-level ineligible-zero and capacity from visible-set feasibility via
  `theorem9ActualEligibleBidders_not_mem_of_not_eligible` and
  `theorem9ActualEligibleBidders_sum_eq`. If the desired payoff is exactly the
  paper's capped normalized spend expression, use
  `BMatchingTheorem9FeasiblePrefixRuleFamily`; it avoids a separate
  capped-revenue field. For integral online b-matching algorithms, use
  `BMatchingTheorem9IntegralPrefixChoiceFamily`, where each deterministic rule
  chooses at most one visible actual bidder per round.
  For the harmonic cap, split the proof into the logarithmic
  tail-spend bound, a finite layer-count comparison, and a separate
  exponential-grid estimate. In `EconCSLib`, these are now represented by
  `theorem9BidderSpendUpperBound_le_log_tail`,
  `theorem9HarmonicLayerCountBound_of_pos`,
  `theorem9ExponentialGridUpperSum_le_msvvRatio`, and
  `theorem9_harmonic_eventually_le_msvvRatio_add`. The finite harmonic cap may
  be above `1 - 1/e`, so state the paper endpoint as an eventual
  additive-`δ` theorem rather than as an exact finite inequality. Package the
  final lower-bound endpoint as a family structure
  (`BMatchingTheorem9FamilyCertificate`, or when using realized allocations,
  `BMatchingTheorem9PointwiseFamilyCertificate` /
  `BMatchingTheorem9SymmetricPointwiseFamilyCertificate` /
  `BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate` /
  `BMatchingTheorem9ObservedPrefixFamilyCertificate` /
  `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate` /
  `BMatchingTheorem9FeasiblePrefixRuleFamily` /
  `BMatchingTheorem9IntegralPrefixChoiceFamily` in `EconCSLib`) so future work
  instantiates only the deterministic choice/allocation rule and, when needed,
  actual-revenue bridge directly. Do not add a
  separate
  harmonic-limit field to new Section 7 family certificates; use the built-in
  harmonic theorem instead.
- Social choice/rankings: use finite rankings/permutations, first/second choice
  accessors, pairwise comparisons, and voting-rule interfaces before hardness
  reductions.

### 2.3 Theorem-Seam Patterns

- For constructive paper proofs, formalize local invariants first, then assemble
  the main theorem by induction or finite recursion.
- If a Lean goal is not moving after a few local attempts, stop expanding the
  proof script in place. Extract the exact algebraic, finite-sum, relabeling, or
  monotonicity fact as a named helper lemma, prove or search for that smaller
  fact, then return to the main theorem. Long inline tactic blocks are usually a
  signal that the theorem seam is too coarse.
- When the paper proof has an informal model bridge, do not over-generalize the
  model before the current theorem is reachable. Add the narrow certificate or
  structure that expresses exactly the missing bridge, prove all surrounding
  algebra unconditionally, and later refine the model by instantiating that
  certificate.
- For finite deterministic-rule optimization statements, first prove a generic
  maximizer-existence theorem over the finite function type `(instances →
  actions)`. Then keep paper folders responsible only for defining the
  paper-specific real-valued objective and applying the generic existence
  result.
- For proofs whose hard part is a known paper lemma, package the lemma as a
  named predicate or certificate and prove the surrounding algebra/induction
  unconditionally.
- For posted-price and prior-free digital-goods auctions, prove truthfulness at
  the threshold-rule level: if the threshold offered to bidder `i` is
  independent of `i`'s own report, accepting iff bid exceeds that threshold is
  DSIC. Then instantiate random-sampling or market-price auctions by proving
  the relevant own-bid-independence lemma. For fixed-price benchmarks, define a
  finite bidder-value candidate benchmark early; the remaining paper lemma is
  then the reduction from arbitrary feasible prices to bidder-value prices.
  For random-sampling digital-goods auctions, first prove the deterministic
  cross-sample threshold mechanism truthful for an arbitrary fixed partition;
  only after that add probability over partitions and revenue approximation.
  The fixed-price benchmark reduction should use the minimum accepted bidder
  value: raising a feasible price to that value preserves the sale count lower
  bound and weakly increases revenue.
  Use a nonnegative offer-price wrapper around finite candidate prices so
  no-positive-transfer and expected-revenue nonnegativity proofs do not inherit
  infeasible negative candidate values from empty samples.
  When the approximation proof is too large for the current pass, package it as
  a named certificate whose statement is exactly the benchmark/revenue
  inequality needed by the paper-facing theorem.
- For GSP/position-auction work, first formalize `PositionOutcome` with
  per-click payments, utility, revenue, welfare, and feasibility. A concrete
  non-truthfulness witness is a good first theorem before building a generic
  bid-sorting mechanism and equilibrium comparisons. Use local envy-freeness as
  an outcome-level certificate for "no profitable assigned-slot deviation"
  before trying to prove full Nash equilibrium of a sorted GSP mechanism.
- For combinatorial auctions, reuse the fair-division bundle/allocation layer.
  Keep feasibility separate from direct mechanisms because approximation
  algorithms may leave goods unallocated. For single-minded bidders, define the
  bundle-containment valuation before proving greedy allocation or
  critical-value payment theorems. Prove pairwise-disjoint accepted-set
  feasibility separately from greedy optimality; this lets the greedy algorithm
  theorem focus on its acceptance invariant and critical-price monotonicity.
- For inequality-heavy proofs, use certificate structures with fields matching
  the exact nonnegativity, strict positivity, and comparison obligations needed
  by the final theorem.
- For finite rounding arguments, split the proof into reusable layers: a
  generic no-crossing combinatorial theorem, a paper-specific exchange
  certificate that rules out crossings at optima, and a final triangle
  inequality step converting anchor closeness plus rounding closeness into the
  paper's approximation guarantee. If the paper proof uses floor/ceiling
  thresholds around a real optimum, use separate lower and upper anchors rather
  than forcing one integer anchor to play both roles. For separable objectives
  with square-root first-order conditions, discharge abstract exchange
  certificates by proving likelihoods are a positive scale times squared
  shifted targets and that anchors bracket those shifted targets.
- When a paper proof derives a continuous relaxation by Lagrange multipliers,
  verify the normalization algebra before encoding the theorem. Off-by-`m`
  shifts can appear when the derivative depends on `x_t + 1`; keep the theorem
  conditional or log a proof-audit note until the exact discrete rounding bound
  is recovered.
- For LP sparsity results, separate the linear-programming theorem from the
  finite counting consequence. First encode the active-support bound supplied
  by basic feasible solutions, then prove reusable counting lemmas such as:
  if every item has an active type and total active type-item pairs are at most
  `n + K - 1`, then at most `K - 1` items can be shared by multiple types.
  For normalized min-item-fairness objectives, positive item fairness usually
  discharges the "every item active" side condition: if an item has no positive
  support, its raw and normalized item utility are zero, contradicting a
  strictly positive finite minimum. Keep the remaining LP/BFS active-support
  theorem as the separate hard seam.
  To prove the paper's `IF* > 0` lemma, use the uniform finite PMF as an
  explicit witness: with strictly positive weights/utilities every item has
  positive raw and normalized utility under the uniform policy, so the finite
  minimum is positive and `sSup` is positive once attainable values are bounded
  above by one.
- For strict monotonicity claims, check boundary cases before proving the
  general theorem. Bernoulli/probability variance terms often become
  identically zero at `q = 0` or `q = 1`, so a paper statement that says
  "strictly decreasing" may need an explicit interior assumption. Also prove
  the corresponding weak monotonicity theorem on the closed interval when it is
  true; that is usually the paper-safe replacement.
- Prefer sum-level certificates when the theorem is about a total expectation
  or finite sum. Do not impose candidatewise nonnegativity merely because it
  would make a `sum_univ_pos_of_pos_of_nonneg` proof convenient; in ranking and
  Mallows-style arguments, non-center fibers can have negative gap mass even
  when the total theorem is true.
- For Mallows/ranking proofs, match the paper's pairwise decomposition when the
  argument compares `(i,j)` and `(j,i)` top-two events. First prove the exact
  top-two expansion of the finite sum, then define the ordered-pair term and
  prove the antisymmetric swap identity. Discharge the remaining proof through
  bracket inequalities for `(i,j)` plus `(j,i)`. This is safer than forcing
  first-choice fiber signs.
- For Mallows proofs, separate three layers explicitly:
  1. the denominator-cleared paper sum,
  2. the top-two pair/bracket regrouping,
  3. the rank-factorization formulas for first/top-two Mallows fibers.
  Prove the algebra from layer 3 to layer 1 before attempting the finite
  permutation bijections that instantiate layer 3. This keeps proof search
  focused and prevents repeatedly reopening already-proved expectation
  decompositions.
- Check strictness and boundary cases before claiming a Mallows theorem is fully
  assumption-free. Strict weaker-competition conclusions cannot follow from
  non-strict equal-parameter comparisons, and independent-reranking positivity
  can fail or become equality in two-candidate edge cases. State the required
  interior parameter and candidate-count assumptions explicitly at the
  paper-facing wrapper, then prove them away only when the paper supplies a
  genuine witness.
- For weaker-competition Mallows sums, do not assume every `(i,j)`/`(j,i)`
  cross bracket is nonnegative unless the algebra has been checked. Unlike the
  independent-reranking bracket, individual cross brackets can be negative while
  the total adjacent-gap/majorization sum is positive. Use prefix/adjacent-gap
  coefficients or another total-sum certificate for that part.
- For adjacent Mallows cross coefficients, the split into shifted suffix weight
  times weighted prefix cross-delta, minus prefix weight times weighted suffix
  cross-delta is useful as a diagnostic. Do not try to close Theorem 3 by a
  global weighted-suffix nonpositive claim: that sufficient condition is too
  strong in general. For weaker-competition Mallows totals, prefer the paper's
  conditional-gap and monotone-likelihood-ratio route.
- For Mallows first-choice dominance, prove the pure geometric prefix lemma
  once, then lift it through rank factorization. The useful pattern is a
  pair-sum regrouping of
  `prefix(qA) * total(qH) - prefix(qH) * total(qA)` into center-ordered
  cross-prefix terms `qA^i*qH^j - qH^i*qA^j`, discharged by a reusable
  rank-power comparison for `qA < qH`. This avoids redoing stochastic-dominance
  algebra at each probability/cross-weight wrapper.
- For Mallows singleton-removal monotonicity, reduce to the rank-only
  best-after-removal weights and prove pairwise cross-ratio dominance. The
  useful split is: removed rank has zero weight; ranks on the same side use the
  usual power MLR after factoring a common positive term; the cross-boundary
  case uses the deletion power sum identity
  `S(q,k) * (1-q) = 1 - q^(n+1)` to prove the boundary factor
  `(S_A+qA^k)*(qH*S_H+qH^k) >= (qA*S_A+qA^k)*(S_H+qH^k)`, then combines it
  with the power comparison for the shifted suffix exponent.
- For Mallows weaker-competition totals, use the paper's conditional-gap route:
  define the rank-only conditional gap, prove it is strictly antitone by
  adjacent-rank comparison, prove the finite MLR weighted-average inequality by
  pair-sum regrouping, and combine it with the positive same-human
  square-weighted conditional gap. Once this closes at the rank-factorized
  layer, construct finite permutation fibers directly rather than leaving a
  structure assumption. For ranking fibers over `Fin`, normalize first-choice
  rank `r` with `Fin.cycleRange r`; normalize ordered top-two ranks `r < s`
  with `cycleRange r` followed by `cycleIcc 1 s`; normalize swapped top-two
  ranks with `cycleRange s` followed by `cycleIcc 1 (r+1)`. Prove the Kendall
  exponent shifts separately, then lift the finite sums through a `sum_bij`.
- When clearing positive probability denominators, expose the unnormalised
  numerator as a reusable definition and prove an equality from the normalized
  expectation to numerator divided by a positive denominator. Also prove the
  positivity equivalence in both directions, so later certificate interfaces can
  move freely between normalized probabilities and denominator-cleared finite
  sums.
- For AdWords and generalized online matching, use the LP-duality theorem seam
  before attempting the full `1 - 1/e` proof. Prove weak duality once from
  `DualFeasible`, then package the algorithm analysis as a
  `PrimalDualCompetitiveCertificate` with fields for primal feasibility,
  nonnegative ratio, dual variables, dual feasibility, and the scaled
  dual-objective bound. The remaining Balance/MSVV work should construct that
  certificate from the query-history fold; run feasibility should already be
  closed through a generic `ChoiceRuleFeasible` theorem. The small-bids limit
  should be a separate paper-local theorem, not mixed into the finite LP layer.
- For symmetry/type-reduction arguments, prove the generic fiber facts first:
  weighted sums by type-cardinality equal sums over original agents, and finite
  minima over agents equal finite minima over types when representatives witness
  every fiber. Then paper reductions become mostly rewriting. For optimization
  reductions, separate exact functional preservation from supremum reasoning:
  first prove lift/descend preservation, then prove symmetrization dominance
  (same item feasibility and weakly better objective), then prove the `sSup`
  equality from explicit nonempty/bounded-above feasible-value side conditions.
  Avoid opaque assumptions such as "the optimal values are equal" when they can
  be replaced by this order-theoretic reduction.
- For normalized utility objectives, prove boundedness before attempting
  compactness. A finite PMF expectation of row utilities is at most the finite
  row maximum, so positive normalizers usually give normalized utility `≤ 1`
  and immediately discharge `BddAbove` obligations for feasible value sets.
- For baseline constrained problems with constraint level `γ = 0`, first check
  whether the constraint reduces to nonnegativity. If objectives are normalized
  nonnegative utilities, prove each normalized coordinate is nonnegative, take a
  finite-minimum nonnegativity lemma, and witness nonemptiness with an arbitrary
  default policy. In type-reduction models, transfer nonnegative utilities
  through representatives and nonnegative type weights through fiber
  cardinalities.
- For finite exchange arguments, avoid re-proving whole objective sums by hand.
  Use a generic two-point finite-sum update lemma: if two functions differ only
  at `src` and `dst`, the total sum changes by the two pointwise deltas. Then
  derive first-order inequalities at finite optima from "no profitable
  exchange" rather than restating optimality from scratch.
- For recommendation diversity/homogeneity papers, split the proof into three
  layers. First prove finite exchange or first-order conditions that force
  pairwise count balance. Then prove a generic representation lemma converting
  count error, such as `|count t - N / T| <= 1`, into share error, such as
  `1 / N`, for the paper's `gamma`-homogeneity profile. Only then attack the
  asymptotic/order-statistic layer. For symmetric i.i.d. Bernoulli items, the
  finite balance proof should cancel the common positive likelihood-success
  coefficient and use strict antitonicity of `(1 - q)^k` when `0 < q < 1`.
  For uniform `[0,1]`, `k = 1` recommendation values, use the closed form
  `1 - 1 / (q + 1)` for the expected maximum of `q` samples. Its forward
  marginal is `1 / ((q + 1) * (q + 2))`, and its positive-count backward
  marginal is `1 / (q * (q + 1))`. Proposition-style square-root homogeneity
  should be separated into: exact marginal algebra, a square-root target-profile
  representation bridge, and then the real-relaxation/integer-rounding theorem.
  For rounding lemmas, first isolate the generic combinatorial fact: if an
  integer vector has no high/low crossing around integer anchors and the anchor
  total is within one type-cardinality of the target total, then every count is
  within one type-cardinality of its anchor. The paper-specific analytic work is
  proving that optimality of the separable objective rules out the crossing. A
  useful intermediate certificate is a strict boundary exchange comparison:
  the loss from removing a high-anchor item is strictly smaller than the gain
  from adding a low-anchor item, uniformly over high/low pairs.
- For finite fair-division allocation theorems, first prove the theorem for an
  abstract marginal bound. Then add a paper-facing corollary instantiating the
  bound as the finite maximum one-good marginal value.
- For finite fixed-total count-allocation optimization, encode feasible
  allocations as functions into `Fin (N + 1)` plus a total-sum proof. Optimize
  over that finite code space, then decode back to the paper allocation type.
  This is often enough to discharge "there exists an optimum" seams before
  invoking exchange or first-order conditions.
- For algorithmic statements, separate the existence/correctness theorem from
  runtime or complexity claims unless the complexity layer is already in scope.
- When a theorem is conditional, name the remaining seam mathematically, not as
  an implementation excuse. Good names describe the paper lemma being assumed.

### 2.4 Lean Proof Patterns

- For finite singleton indicator sums, use:

```lean
simpa using
  (Finset.sum_ite_eq' Finset.univ key
    (fun _ => weight))
```

- For sums of divisions in real-valued finite sums, import
  `Mathlib.Algebra.BigOperators.Field` and use `Finset.sum_div`.
- For `PMF` over finite types, prefer existing finite-expectation lemmas and
  `pmfExp`/`pmfProb` abstractions over hand-expanding `PMF` internals.
- For finite analytic PMF families, prove continuity at the atom level
  `fun θ => ((μ θ) a).toReal`, then lift through a finite expectation lemma
  such as `epsilonContinuousAt_pmfExp_of_atom`. Do not import broad topology
  just to prove a finite epsilon-delta continuity bridge.
- When a compact-interval theorem needs mathlib `ContinuousOn`, convert a
  pointwise epsilon-delta interface with a small bridge such as
  `continuousOn_of_forall_epsilonContinuousAt`; keep the topology import in the
  generic interval/analysis module, not in every paper file.
- For uniform PMFs over finite spaces, derive relabeling invariance with
  `pmfExp_uniformPMF_comp_equiv` or
  `pmfExp_uniformPMF_eq_of_comp_equiv` instead of expanding the uniform mass by
  hand. For the AdWords permutation distribution, use
  `uniformPermutationExpectation_eq_of_relabel`.
- For pure PMF cases, use lemmas such as `pmfExp_pure`,
  `pmfPairExp_pure_left`, and `pmfPairExp_pure_right` when available.
- When a proof branches on an abbreviation but the goal expands it, normalize
  with local facts:

```lean
have h' : c = rawExpr := by simpa [abbrevName] using h
```

- For pair events, convert each component explicitly:

```lean
have hc : c = rawFirst := by simpa [firstAbbrev] using h.1
have hd : d = rawSecond := by simpa [secondAbbrev] using h.2
```

- To transport hypotheses across equality of reference structures, rewrite the
  reference explicitly rather than hoping `simp` finds it.
- Mark definitions `noncomputable` when they depend on real comparisons,
  filtered finite sets over propositions, `PMF` normalization, or classical
  choice.
- Keep imports narrow. Prefer specific Mathlib modules over `import Mathlib` in
  new or actively repaired files.
ively repaired files.
� → ℝ`) rather than jumping immediately to measure-theoretic random variables. This allows explicit expected-value decompositions (like Variance/Bias MSE splits) to be proven using straightforward finite summation algebra (`pmfExp`).
- Keep imports narrow. Prefer specific Mathlib modules over `import Mathlib` in
  new or actively repaired files.
ively repaired files.
ures, rewrite the
  reference explicitly rather than hoping `simp` finds it.
- Mark definitions `noncomputable` when they depend on real comparisons,
  filtered finite sets over propositions, `PMF` normalization, or classical
  choice.
- Keep imports narrow. Prefer specific Mathlib modules over `import Mathlib` in
  new or actively repaired files.
ively repaired files.
