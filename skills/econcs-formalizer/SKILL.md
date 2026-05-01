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
- For LP-heavy papers, prefer a paper-local equality-form, certificate, or BFS-witness interface when that is enough to follow the paper proof and close named results. Build a generic LP/simplex/duality layer only when the current theorem truly needs it or a second paper will immediately reuse it; otherwise keep the optimization boundary narrow and auditable in the paper folder.

### 1.3 Paper Folder Contract

Each paper-specific folder should be auditable by a human who wants to compare
the Lean statements against the paper.

- **Required Template Structure:** Every paper folder must strictly follow the `papers/TEMPLATE/` format. This includes:
  1. A `README.md` (see details below).
  2. A `DependencyDAG.tex` providing the proof roadmap.
  3. A `MainTheorems.lean` file holding the paper-facing wrappers.
  4. A local `.gitignore` file.
- **Local Gitignores:** Every paper folder *must* contain its own `.gitignore` that explicitly ignores `*.pdf`, `*.aux`, `*.log`, `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`. The overall repo `.gitignore` may contain generic LaTeX auxiliary patterns such as `*.aux`, `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`, but should not contain paper-specific PDF exclusions or paths.
- **Reproducible PDF and text cache:** A copy of the source PDF must be downloaded once and kept in the local paper folder so humans and agents can read exactly what is being reproduced. Immediately run `pdftotext Source.pdf Source.txt` in the same folder and use that cached text file for named-statement searches. Because of the local `.gitignore`, the PDF will not be committed to Git, preventing repository bloat; the `.txt` cache should remain beside the PDF unless the paper has a copyright or licensing reason not to track extracted text. Work from these local files; do not repeatedly search the web or re-run extraction unless the source PDF changes.
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
- **One citation per paper folder:** Do not use aggregate folders for award lists, reading lists, or multi-paper campaigns. Split them into one `[AuthorInitials][2DigitYear][Descriptor]` folder per source paper, each with its own source PDF/text cache, README, DAG, and `MainTheorems.lean`. If an aggregate module already exists, keep it only as a compatibility import or handoff note and move paper-facing status into the citation-specific folders.
- **Initial Proof Roadmap (Dependency DAG):** At the *very beginning* of formalizing a new paper, before writing any deep proof code, you must create a comprehensive proof roadmap. Read through the paper carefully to identify *every* named result (Definitions, Lemmas, Propositions, Theorems, Corollaries) and map out exactly how they relate to each other. Encode this roadmap as a dependency DAG in a TikZ source file (with a rendered image) in the paper folder. This ensures no named result is overlooked, helps you understand the overall proof architecture, and gives humans a clear audit of the theorem flow.
  - **Project pattern in this repo:** for Monoculture, keep the active artifact at
    `papers/KR21Monoculture/DependencyDAG.tex` and a rendered image alongside it.
  - All paper DAGs MUST `\input` the shared preamble located at `docs/tikz/dag_preamble.tex`.
  - Use the exact node styles defined in the preamble: `dag_result` (green), `dag_lemma` (yellow rounded), `dag_model` (blue ellipse), `dag_unformalized` (dashed gray), `dag_conditional` (orange rounded), and `dag_caveat` (red diamond).
- **DAG Formatting and Clarity Mandates:**
  - The DAG must encode formalization status and node type explicitly by using the preamble styles.
  - **Node Content:** Node text MUST begin with a bolded header indicating the Theorem/Lemma/Definition name and, if available, its location in the paper (e.g., `\textbf{Theorem 1 (Section 4)} \\ Description` or `\textbf{Lemma 12 (App. E)} \\ Symmetry reduction`). Provide a brief, readable description on the following line(s).
  - **Legend:** You MUST include a Legend using the shared helper macro from the preamble, e.g., `\daglegend{(legRes)(legLem)(legDef)(legOpen)}{Legend}`. Place legend nodes concisely at the top.
  - **Edge Routing (No Overlaps):** Use explicit positioning (`node distance`, `below=of`, `right=of`, `xshift`, `yshift`) carefully. **Prefer straight paths or simple orthogonal routing (`|-`, `-|`) whenever possible without overlap.** Use a column-based layout (the preamble standardizes horizontal spacing at `3cm` or `4cm` depending on the specific diagram needs) to ensure paths are clear and text boxes do not collide. Only use complex curves (`to[out=..., in=...]`) or bends when absolutely necessary to route around an immediate obstacle. Use `dag_arrow` and `dag_dashed_arrow` from the preamble for styling.
- Keep the DAG updated after every major paper update (for example: a named
  paper theorem/lemma closed, a dependency refactor that changes proof flow, or
  a status transition between scaffold/conditional/formalized).
- A downstream theorem node may use the green `dag_result` style only when its
  paper-facing statement is closed without remaining paper assumptions. If Lean
  currently proves only wrappers conditional on certificates, no-gap hypotheses,
  selected-BFS assumptions, or witness existence, use `dag_conditional` for the
  wrapper and add a separate `dag_unformalized` node for the full paper theorem.
  The node text must name the exact open certificates or witnesses.
- In this repository's `papers/[Paper]/DependencyDAG.tex` layout, the shared
  preamble input is `\input{../../docs/tikz/dag_preamble.tex}`. Verify the DAG
  renders after changing the preamble path or moving a paper folder.
- If a theorem is only conditional, the README must name the exact certificate
  or assumption declaration that remains. Do not describe it vaguely as
  "technical details".
- Use source-numbered paper declaration names only for statements that are
  source-faithful. If Lean proves an auxiliary finite analogue, certificate
  interface, or deliberately weakened bridge, name it as an auxiliary
  declaration (for example `paper_aux_*` or a name that explicitly says
  `finite_analogue`) and mark the source theorem as partial/open in the README
  and DAG.
- The paper `README.md` is the live status ledger and handoff document for
  partial progress. A `FINAL_VALIDATION_REPORT.md` is not a handoff note; it is
  the final one-page human assessment created only when making a final claim
  about a paper or completed proof phase. It must answer whether the paper is
  verified, what additional assumptions were needed, whether mistakes were
  found, and whether the Lean proof followed the paper strategy or used a
  different route.
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
- Prioritize finishing the theorem over creating frequent checkpoints. Once the
  finite scaffold is stable, spend effort on the hard remaining bridge rather
  than packaging every helper lemma as a separate commit or documentation pass.
  Commit only when a substantial named result is genuinely closed, when moving
  papers, or when the user explicitly asks for a checkpoint.
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

3. Choose the model level that closes the theorem fastest.
   EC papers often have useful finite entry points: finite agents, items,
   actions, rankings, allocations, mechanisms, PMFs, and finite sums. Use those
   when they expose the key combinatorics cleanly. But do not force a finite
   analogue first if the paper theorem is genuinely continuous and the direct
   continuous statement is shorter or more faithful. For density, RUM,
   distributional, or integral inequalities, formalize the continuous version
   directly when that avoids a long detour through artificial finite scaffolding.
   When the paper proof is a change-of-variables argument over densities,
   consider adding a reusable library-level measure lemma first, e.g. a
   `withDensity` mass comparison under a measure-preserving measurable
   equivalence. This can be faster and closer to the paper than reifying the
   same argument through artificial finite PMFs, especially for continuous RUM
   proofs.
   For strict continuous analogues of finite atom-witness arguments, use a
   positive-measure source subset plus a finite source integral. In Lean this
   often means a reusable `withDensity` strict comparison lemma with assumptions
   like `Measurable D`, `∫⁻ x in source, D x ∂μ ≠ ∞`, and `μ source ≠ 0`.
   Remember to `open scoped ENNReal` in files that state `ℝ≥0∞` or `∫⁻`
   expressions; otherwise parser errors around `∂`/`∞` can waste time.
   When a continuous distribution ultimately feeds a finite theorem over
   rankings, push the continuous measure through the ranking map and convert the
   finite pushed-forward measure to a `PMF`. Then prove a small bridge saying
   `pmfProb` equals the continuous preimage mass. This lets existing finite
   payoff algebra consume actual continuous ranking laws while the analytic
   density comparisons stay in the continuous measure layer.
   For continuous delta inequalities that compare differences of event
   probabilities, avoid hand-proving signed measure decompositions when the
   relevant events depend on a finite summary. Push the measure through the
   finite image of that summary, apply the finite indicator-difference lemma
   there, and pull the result back with a `measureProb` bridge. The pointwise
   comparison then only needs to hold on source realizations, not on every value
   of the finite codomain.
   For continuous `swapi`/change-of-variables arguments, split the proof into
   two layers: first a reusable `withDensity` mass comparison under a
   measure-preserving measurable equivalence and density monotonicity, then a
   paper-local score-geometry wrapper proving that the source transition region
   maps into the target transition region and supplies the coordinate-order
   inequality used by the density lemma.
   For normalized continuous score laws, expose the probability-measure
   assumption through the natural integral equation `∫⁻ x, D x ∂μ = 1` and a
   small `IsProbabilityMeasure (μ.withDensity D)` bridge. This keeps final
   theorem statements closer to the paper's "density integrates to one" premise
   and avoids hiding normalization as an opaque typeclass-only requirement.
   The same normalization equation should also discharge any strict-swap
   side condition requiring a source-set integral to be finite, since
   `∫⁻ x in s, D x ∂μ ≤ ∫⁻ x, D x ∂μ = 1`.
   Separate continuous RUM proofs into explicit layers before calling a paper
   done: (i) payoff/certificate algebra over rankings, (ii) continuous
   density/change-of-variables inequalities over scores, and (iii) concrete
   model instantiation proving support, positive source regions, normalization,
   and score-to-ranking interface facts. A closed theorem at layer (i) or (ii)
   is valuable progress, but it is not a fully concrete paper theorem until
   layer (iii) has no remaining assumptions or the README/DAG say exactly which
   assumptions remain.
   Treat ties in real-valued score RUMs as a theorem-design issue, not a detail
   to patch later. Pointwise "top score iff top-ranked" interfaces can be false
   or inconsistent on tie points. Either work on a no-tie/full-measure subtype,
   state and prove almost-everywhere interface lemmas, or make the tie-breaking
   convention explicit and prove the score/ranking facts for that convention.
   Do not silently derive pointwise ranking-event implications from weak score
   inequalities.
   After an abstract `withDensity` proof compiles, immediately add concrete
   score-space utilities for the intended product space: coordinate projection
   abbreviations, measurable coordinate swaps, measure-preserving swap lemmas,
   normalization bridges, and finite-source-integral bridges. Align the product
   nesting with Mathlib's product measure conventions, e.g. `(ℝ × ℝ) × ℝ`, so
   later instantiations do not spend time on associativity rewrites.

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
- Do not infer that downstream files are broken until the direct imported module
  builds.
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

Before declaring a paper or proof phase "done," run a final human-facing
validation pass:

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
  artifacts (TikZ source and rendered image). This report is not for routine
  handoff; it is the concise final assessment a human should read to decide what
  was actually verified.
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

## Component 2: Proof Reference Routing

Do not load one giant theorem-proving playbook. When starting a nontrivial Lean
proof, read only the reference for the library layer being touched; if the proof
crosses layers, read at most the generic foundation reference and one domain
reference.

| Touched code | Read |
|---|---|
| `EconCSLib/Foundations/Math/*`, graph/counting/rounding/sign lemmas | `references/proof-foundations-math.md` |
| `EconCSLib/Foundations/Probability/*`, finite PMFs, continuous densities, RUM/noise laws | `references/proof-foundations-probability.md` |
| `EconCSLib/Foundations/Optimization/*`, argmax/existence/objective wrappers | `references/proof-foundations-optimization.md` |
| `EconCSLib/Applications/RecommenderSystems/*`, accuracy/diversity, producer fairness, count allocation | `references/proof-recommender-systems.md` |
| `EconCSLib/Algorithms/Online/*`, AdWords/MSVV, online matching, regret/Yao | `references/proof-algorithms-online.md` |
| `EconCSLib/MechanismDesign/Auctions/*`, digital goods, GSP, combinatorial auctions | `references/proof-mechanism-design.md` |
| `EconCSLib/Markets/*` or `EconCSLib/SocialChoice/*`, matching, fair division, rankings/Mallows | `references/proof-markets-social-choice.md` |

`references/proof-strategies.md` is only a short router/index for these files.
Do not load detailed proof references for routine README/DAG/status edits or
simple wrapper repairs.
