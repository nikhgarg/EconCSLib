---
name: econcs-formalizer
description: Formalize economics-and-computation papers in Lean. Use when asked to add, continue, triage, or plan Lean formalizations of EC/ACM EC/SIGecom-style papers; formalize finite, continuous, probabilistic, or measure-theoretic theorem seams; extract reusable primitives; repair Lean/mathlib proof scripts; or prepare general handoff guidance for future formalization work.
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

Unless told otherwise, you do not have a time limit; keep going until you fully
finish a paper and run the post-paper checklist.

Do not confuse "keep going" with broad exploration. Move in tight compile/proof
loops: identify the exact current theorem seam, make the smallest coherent
batch of edits, run only the requested or necessary targeted build, and patch
the compiler's concrete line errors. Avoid rereading large files after you
already know the relevant structure; use `rg` for exact declaration names and
narrow line windows around compiler diagnostics.

When another agent will pick up later, spend tokens on durable artifacts rather
than chat: a paper-local handoff note, README/audit links, exact declaration
names, validation status, and next command. Future agents should start from
those files instead of reconstructing context from conversation history.
For a pause of several days or longer, create or refresh a paper-local
`START_HERE_NEXT_AGENT.md` that is shorter than the full handoff: current
validation commands, shared-worktree caveats, the exact active proof seam,
strongest reusable endpoints, and what not to work on next. Link it from the
paper README, audit/final-validation report, and front repository status so a
future agent has one obvious startup path.
If a paper is being paused for a stronger future model, say that explicitly in
the paper README/handoff and in the front repository status entries. Name the
three or fewer exact proof seams that remain and the strongest public wrapper or
certificate for each. Do not leave vague optimistic status such as "one bridge
remains" when multiple paper-level proof campaigns are still open.

When a proof is blocked, think outside Lean as needed, patch the mathematical
argument yourself, and then implement the patched proof in Lean. Do not stop at
identifying the gap unless the target theorem is false or the needed assumption
is mathematically indispensable.

If a paper proof is imprecise, think hard outside Lean to create a precise proof
strategy, implement that strategy in Lean, and log in the paper's final report
that the source proof was imprecise and needed additional formalization work.

When the right proof strategy is unclear, think deeply outside Lean before
editing. If a written scratch argument would help, create a short `.txt`,
`.tex`, or `.md` sketch in the paper folder; keep it only as detailed as needed
to unlock the Lean proof. Do not create a sketch when it would be ceremony
rather than useful proof planning. After the strategy is clear, execute it in
Lean and keep moving.

Keep strategy notes token-cheap. A good scratch update is the active theorem
name, the exact remaining mathematical obligation, the next bridge lemma, and
the validation command. Do not copy long proof states, full diffs, or entire
README tables into handoffs when declaration names and file links identify the
same information.

Do not avoid continuous, probabilistic, or measure-theoretic formalization when
the source theorem requires it. Finite analogues are useful scaffolds only when
they shorten the faithful proof. If the fastest honest route is a direct
measure/integral/renewal/CTMC statement, build that statement directly and keep
the paper-facing wrapper source-level.

Keep theorem-specific proof tactics out of this always-loaded file. Use the
reference routing table at the end: CTMC/reward-rate details live in
`references/proof-foundations-probability.md`; dynamic-game/PBE certificate
details live in `references/proof-mechanism-design.md`; matching and
Plackett--Luce details live in `references/proof-markets-social-choice.md`.
When updating the skill, treat this as an invariant, not a preference: if the
new lesson names a specific paper, theorem number, counterexample, proof
recipe, or declaration family, it belongs in a reference file unless it is only
a one-line routing pointer.

When starting a new paper, briefly inspect the repository's already-formalized
papers in the same EC area and ask which proof moves should become general
library tools. Do not force a detached library project before proving the paper,
but if a lemma, interface, or theorem is likely to be useful to another EC paper,
build it in `EconCSLib` while formalizing the current result.

When starting a paper, do an outside-Lean proof-planning pass over the entire
proof and formalization route before deep Lean implementation. Identify the
main theorem chain, likely reusable library seams, underspecified paper steps,
necessary assumptions or certificates, and fallback proof paths. Use the
scaffolded `FORMALIZATION_PLAN.md` in the paper folder as the live plan, or use
`.txt`/`.tex` instead only when that is genuinely more convenient. Keep it short
and functional: it is a scratchpad for thinking, not a polished deliverable.
Then start executing the plan in Lean. As the formal proof progresses, edit the
plan to record strategy changes, patched source gaps, discharged seams, and
remaining blockers.

For long or fragile proofs, keep a theorem-specific scratch plan beside the
paper files and use it actively, not as decoration. A good plan records current
Lean endpoints, the exact mathematical gap, the next two or three bridge lemmas,
why each bridge should be true, and which assumptions are source assumptions
versus temporary certificate fields. Put domain-specific certificate patterns in
the relevant proof reference file, not here.
When a long session ends before validation, write a paper-local handoff note
before stopping. Include the files touched, the latest unvalidated theorem
families, the intended proof route, exact next validation command, and likely
fragile Lean points. Link that handoff from the paper README and post-paper
audit report so a future agent does not need chat context.
After validation succeeds, immediately update the handoff/status language from
"unvalidated" to the exact command that passed. Do not leave stale caveats that
force the next agent to rerun work just to learn whether the current additions
compile.
For dynamic-game, PBE, strategy, payoff, or schedule-certificate proof details,
load `references/proof-mechanism-design.md` instead of putting theorem-specific
guidance here.

Follow the original paper's proof structure as closely as is practical. Preserve
named definitions, lemmas, propositions, and theorem numbers in Lean declaration
names, docstrings, and README status rows. When deviating from the paper proof
because Lean needs a reusable intermediate lemma or a cleaner finite/discrete
interface, make the deviation explicit and keep the paper-facing wrapper close
to the original named result.

When a source proof explicitly routes a theorem through named paper lemmas or a
named proof-line corollary, prefer formalizing that named route when it is
reasonably available. Do not spend unbounded time following the exact proof line
by line if a different or more precise argument proves the same paper-facing
statement cleanly. In that case, keep the named theorem/lemma structure in the
README, DAG, audit wrappers, and declaration names where practical; state the
same theorem; and log the route change in `FINAL_VALIDATION_REPORT.md` under
`Proof-Strategy Deviations` as a proof deviation. Do not replace a named-lemma
path with a looser certificate, alternate theorem, or broad abstraction unless
the resulting paper-facing endpoint still states the source result or the source
route is false, imprecise, or genuinely inapplicable. If an auxiliary
certificate is temporarily useful, keep it as a clearly marked staging device
and continue toward the paper's named theorem itself.

For stable-matching/deferred-acceptance papers, load
`references/proof-markets-social-choice.md` after the first status pass. It
contains the matching-specific assumptions, strict-preference notation checks,
DA infrastructure guidance, manipulation-rank warning, and IM05 repair notes.

### 1.2 Library Layering Rule: Textbook vs. Audit Trail

Think of the repository as having two distinct roles: **`EconCSLib` is the textbook. The `papers/` directory is the audit trail.**

- **`EconCSLib/` (The Textbook):** Put generic, abstracted EC/CS/econ results here. If a definition, algorithm, or theorem is foundational enough that a graduate student should know it, or if a second paper might build on it (e.g., Gale-Shapley, Nash equilibrium, LP duality), it belongs in the core library.
  - **Abstraction:** Code here should be highly abstracted and stripped of paper-specific notation. Use generic types (`α`, `β`) and naming conventions consistent with `Mathlib`.
  - **Lean Style:** Follow `docs/LEAN_STYLE.md`: `UpperCamelCase.lean` module
    names, narrow leaf imports, module docstrings with `## Main declarations`
    for new reusable modules, `UpperCamelCase` structures/predicates,
    `lowerCamelCase` definitions/data, and `snake_case` theorem names.
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
  it can move or unstage other agents' work. Recover with scoped staging,
  follow-up commits, or explicit coordination instead.

### 1.2.1 Paper Link Intake Protocol

When the user provides only a paper link and asks for autonomous
formalization, execute the standard intake before deep proof work:

- Download/cache the exact source PDF in a new or existing
  `papers/[AuthorInitials][2DigitYear][Descriptor]/` folder, then create the
  adjacent `.txt` extraction with `pdftotext`.
- If the paper link is arXiv, also download/cache the arXiv source archive
  (`e-print`) during intake and unpack it beside the PDF/text cache. Prefer
  the TeX source for theorem statements, displayed equations, notation, labels,
  and appendix references; use PDF extraction mainly for quick search and for
  confirming page context.
- If the PDF/text cache already exists in the paper folder, use those local
  files. If an arXiv source cache exists, use it too. Do not search the web
  again, re-download the paper, or re-run extraction unless the cached source
  version is missing, corrupted, or known to be the wrong version.
- When `pdftotext` output is garbled for formulas, stop trying to reconstruct
  the formula from layout text. Read the cached TeX source directly and cite
  the source line/macro in the paper-facing comment or plan note when it
  changes the Lean statement.
- Read the abstract, introduction, model section, and theorem statements first;
  then search the cached text for every named `Definition`, `Lemma`,
  `Proposition`, `Theorem`, `Corollary`, and appendix result.
- Create the paper folder contract artifacts immediately: `README.md`,
  `DependencyDAG.tex`, `MainTheorems.lean`, and local `.gitignore`.
- Draft paper-facing theorem signatures before building a helper tower. If the
  direct statement is too hard, create an explicit bridge theorem whose name and
  assumptions describe the remaining gap.
- During intake, classify reusable primitives by library area. Upstream only
  seams that pass the second-paper test, such as finite PMF/Markov kernels/MDPs,
  probability inequalities, monotonicity/comparison lemmas, allocation
  primitives, or mechanism interfaces.
- Keep a live README status table from the first scaffold onward. Each row must
  distinguish source-faithful wrappers, auxiliary analogues, conditional
  wrappers, and unstarted paper results.

### 1.3 Paper Folder Contract

Each paper-specific folder should be auditable by a human who wants to compare
the Lean statements against the paper.

- **Required Template Structure:** Every paper folder must strictly follow the `papers/TEMPLATE/` format. This includes:
  1. A `README.md` (see details below).
  2. A `DependencyDAG.tex` providing the proof roadmap.
  3. A `MainTheorems.lean` file holding the paper-facing wrappers.
  4. A `PaperInterface.lean` file holding the compact human-facing definitions
     and named theorem statements.
  5. A local `.gitignore` file.
- **Local Gitignores:** Every paper folder *must* contain its own `.gitignore` that explicitly ignores `*.pdf`, `*.aux`, `*.log`, `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`. The overall repo `.gitignore` may contain generic LaTeX auxiliary patterns such as `*.aux`, `*.fls`, `*.fdb_latexmk`, and `*.synctex.gz`, but should not contain paper-specific PDF exclusions or paths.
- **Reproducible PDF/text/source cache:** A copy of the source PDF must be downloaded once and kept in the local paper folder so humans and agents can read exactly what is being reproduced. Immediately run `pdftotext Source.pdf Source.txt` in the same folder and use that cached text file for named-statement searches. For arXiv papers, also cache and unpack the TeX source archive once; use it as the authoritative source for formulas when PDF extraction is ambiguous or garbled. Because of the local `.gitignore`, the PDF will not be committed to Git, preventing repository bloat; the `.txt` cache should remain beside the PDF unless the paper has a copyright or licensing reason not to track extracted text. Work from these local files; do not repeatedly search the web or re-run extraction unless the source PDF or source archive changes.
- **README Requirements:** The `README.md` must clearly identify the exact
  source version of the paper (e.g., arXiv version `vX`, conference year) and provide URLs.
- **DAG Node Wording:** `DependencyDAG.tex` is a proof roadmap for humans, not
  a formalization changelog. Once a node is marked formalized, its text should
  state or briefly summarize the paper claim. Do not fill green nodes with
  implementation notes such as helper families, algebra rewrites, or "closed"
  status language; keep those details in the README status table, proof notes,
  or handoff files. Partial/conditional nodes may mention the missing proof
  obligation, but should still foreground the paper statement. During a pause
  or handoff pass, audit the DAG for this specifically: if a node reads like a
  session log, rewrite it before rendering.
- Add one central Lean file for paper-facing theorem statements, conventionally
  named `MainTheorems.lean`, `PaperTheorems.lean`, or the existing paper root if
  the folder already has a root module. This file should state and prove only
  the main theorem wrappers and import the detailed proof files.
- Main theorem definitions/functions in that central file should mirror the
  paper statement closely enough that a human can inspect just this file and
  verify the intended theorem was formalized. Use paper theorem numbers/names in
  docstrings and keep wrappers thin.
- For large campaigns, add one adjacent Lean declaration ledger file (for
  example `PaperInterface.lean`) that is the single-file human verification
  target for the folder’s claims.
  The file should be declaration-ordered by paper section and should expose the
  paper-facing definitions and full theorem statements (with assumptions and
  short paper-context comments) rather than `#check` entries alone.
- For new papers, create `PaperInterface.lean` during intake from the scaffold,
  not only after the proof is complete. Keep it synchronized with the proof plan
  and DAG so the eventual human review file grows with the formalization.
- When scaffolding a paper (for example through `scripts/new_paper.py`), run
  `python3 scripts/review_dashboard.py --paper <paper-folder> --refresh-cache`
  once so the dashboard snapshot is generated before the first review workflow.
- After declaration-level edits in `PaperInterface.lean` (especially theorem
  statement changes), run the paper-local review launcher (`./review-dashboard.sh`)
  before relying on the trace for those statements.
- The launcher checks freshness against the logged trace on startup; if an old
  check is out of date, it warns you and you can immediately re-save checks.
- It also shows compact paper-source action links (open PDF/text file), so the
  reviewer can quickly jump back to source wording when needed.
- Paper-facing formulas that look like LaTeX are rendered in the dashboard so
  theorem statements are easier to read without full Lean familiarity.
- `./review-dashboard.sh` always regenerates the lightweight Lean→TeX preview from
  the current declarations on launch, so you do not need a separate “translation”
  step.
- On WSL2, if the browser does not open automatically, add `--host 0.0.0.0` and
  open the printed URL first (normally localhost/127.0.0.1). If that fails, try
  the additional host URL if printed.
- To add `review-dashboard.sh` to existing paper folders that already have
  `PaperInterface.lean` but not the launcher yet, run:

  `python3 scripts/bootstrap_review_launchers.py --write`
- **CRITICAL MANDATE - NO HIDDEN DEFINITIONS:** A human reviewer cannot verify a theorem if its core terms are opaque references to generic library modules (e.g., `EconCSLib.Statistics.priorWeightedVariance`). The `PaperInterface.lean` file MUST expose the exact mathematical formulas for the paper's definitions. Do this by defining paper-specific `abbrev`s or `def`s at the top of the interface that spell out the raw formulas exactly as they appear in the paper, and then use those local definitions in your paper-facing theorem statements or prove they equal the generic terms. A reviewer must see the actual math equations inside this single file without needing to open imported generic modules. Keep `PostPaperAudit.lean` for theorem endpoint aliases and proof-seam coverage, not standalone proof-facing formula duplicates.
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
- **Paper Directory and Namespace Convention:** All new paper folders, modules, and internal namespaces MUST be named using the format `[AuthorInitials][2DigitYear][Descriptor]` in PascalCase (e.g., `MSVV07AdWords`, `LMMS04FairDivision`, `KR21Monoculture`). This guarantees collision-proof Lean namespaces while immediately communicating the citation. All paper implementations sit within the `papers/` directory.
- **One citation per paper folder:** Do not use aggregate folders for award lists, reading lists, or multi-paper campaigns. Split them into one `[AuthorInitials][2DigitYear][Descriptor]` folder per source paper, each with its own source PDF/text cache, README, DAG, and `MainTheorems.lean`. If an aggregate module already exists, keep it only as a compatibility import or handoff note and move paper-facing status into the citation-specific folders.
- **Initial Proof Roadmap (Dependency DAG):** At the *very beginning* of formalizing a new paper, before writing any deep proof code, you must create a comprehensive proof roadmap. Read through the paper carefully to identify *every* named result (Definitions, Lemmas, Propositions, Theorems, Corollaries) and map out exactly how they relate to each other. Encode this roadmap as a dependency DAG in a TikZ source file (with a rendered image) in the paper folder. This ensures no named result is overlooked, helps you understand the overall proof architecture, and gives humans a clear audit of the theorem flow.
  - **Project pattern in this repo:** for Monoculture, keep the active artifact at
    `papers/KR21Monoculture/DependencyDAG.tex` and a rendered image alongside it.
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
    different verified path and does not need a paper lemma that remains
    partial/open, the result may be green, but the DAG must not show that
    partial/open lemma as a required solid input. Either omit that non-used
    dependency, mark it as a dashed paper-route/caveat edge, or say in the node
    or README that the paper proof input was bypassed by an alternate formal
    route.
  - If a theorem still requires an unproved assumption, certificate, or earlier
    paper lemma to obtain the paper-level statement, it is **not green**. Use
    `dag_conditional`, `dag_partial`, or `dag_caveat` as appropriate, and make
    the remaining assumption explicit in the node text and README row.
  - **Edge semantics:** Solid `dag_arrow` edges are verified dependencies in the
    formalized proof path. Dashed `dag_dashed_arrow` edges are for paper-roadmap
    dependencies, unresolved/conditional inputs, caveat links, or dependency
    paths that are not yet fully discharged. A dashed edge into a green result
    is allowed only when it is clearly non-required for the formal proof or
    explicitly documented as a bypassed paper route; otherwise the target node
    should not be green.
  - **Paper-route vs formal-route discipline:** If formalization discovers that
    a paper lemma is misstated, too strong, or unnecessary for a later theorem,
    do not silently collapse the distinction. Record the source issue in the
    README/validation report, keep the affected paper lemma partial/caveated,
    and mark any later theorem green only if Lean proves that theorem through a
    fully verified alternate route or through weaker assumptions already
    discharged. If the later theorem merely assumes the problematic lemma, it is
    conditional/caveated, not green.
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
  - **Closed theorem text stays short:** Once a theorem is closed, the theorem
    node should describe the source theorem's statement, not the Lean proof
    machinery that closed it. Do not fill a closed theorem box with internal
    helper names, certificate layers, construction details, or a list of every
    bridge lemma. Put those details in the README status row, final report, or
    proof comments.
    Include the actual source-facing conclusion or a faithful short formula
    summary in the DAG node itself so a human can recognize the paper result
    without opening the Lean file. For example, a closed Gaussian lemma node
    should say that the posterior estimate has the displayed weighted-mean
    formula and normal law, not merely that "Gaussian algebra was proved."
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
  - **Edge Routing (No Overlaps):** Use explicit positioning (`node distance`, `below=of`, `right=of`, `xshift`, `yshift`) carefully. **Prefer straight paths or simple orthogonal routing (`|-`, `-|`) whenever possible without overlap.** Use a column-based layout (the preamble standardizes horizontal spacing at `3cm` or `4cm` depending on the specific diagram needs) to ensure paths are clear and text boxes do not collide. Only use complex curves (`to[out=..., in=...]`) or bends when absolutely necessary to route around an immediate obstacle. Use `dag_arrow` and `dag_dashed_arrow` from the preamble for styling.
  - For dense paper DAGs, prioritize a visually auditable named-result topology
    over drawing every redundant instantiation arrow. If a theorem node already
    states that it satisfies particular definitions or conditions, it is
    acceptable to omit duplicate long cross-edges when those edges would create
    text or box overlap; keep the exact status and remaining assumptions in the
    node text and README row.
- Keep the DAG updated after every major paper update (for example: a named
  paper theorem/lemma closed, a dependency refactor that changes proof flow, or
  a status transition in the controlled README/DAG vocabulary).
- Keep the paper DAG paper-facing. Its primary nodes should be the source's
  named definitions, lemmas, propositions, theorems, and corollaries. Do not
  replace a source theorem with internal implementation layers such as finite
  analogues, certificate packages, or continuous instantiation steps unless the
  source itself is organized that way. Put those engineering layers in the
  README status table or proof comments, and use the DAG to show how the
  paper's named results relate and which of them are formalized, conditional,
  caveated, or open.
  If the source has only a few named results, keep the DAG correspondingly
  simple; do not compensate by adding a large set of paper-unnamed Lean helper
  nodes.
  Even when the working proof closes a finite analogue first, the DAG should
  still show the corresponding source theorem node with the honest paper-level
  status; finite versions belong in Lean helper names, README rows, or proof
  comments, not as replacement DAG nodes.
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
  independence/Fubini/density derivation), keep the theorem conditional in the
  README/DAG and explicitly name the probability-to-integral bridge that remains.
- For sequential weighted without-replacement or "first distinct draw" models,
  load `references/proof-foundations-probability.md`; for matching-specific
  Plackett--Luce/IM05 details, also load
  `references/proof-markets-social-choice.md`.
- When a proof step invokes an external cited analytic theorem that is not in
  Mathlib, encode that input as a named paper-local hypothesis or definition
  (for example, a `Sampford...Bound` assumption), prove the source's downstream
  reduction from that exact hypothesis, and keep the README/DAG conditional
  until the cited theorem itself or an acceptable imported library theorem is
  formalized.
- When such a cited theorem is later formalized locally, immediately update the
  paper README/DAG to remove that exact assumption while preserving any broader
  remaining bridge. For example, if a scalar density/integral layer is now
  unconditional but the source theorem is still a probability statement, mark
  the scalar layer as closed and keep only the probability-to-integral bridge as
  the theorem-level blocker.
- In this repository's `papers/[Paper]/DependencyDAG.tex` layout, the shared
  preamble input is `\input{../../docs/tikz/dag_preamble.tex}`. Render from the
  paper folder (`cd papers/<Paper> && latexmk -pdf DependencyDAG.tex`) or use a
  LaTeX invocation that preserves that relative path; running `latexmk
  papers/<Paper>/DependencyDAG.tex` from the repo root resolves the preamble
  relative to the wrong directory and wastes a build cycle. Verify the DAG
  renders after changing the preamble path or moving a paper folder.
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
- If a theorem is only conditional, the README must name the exact certificate
  or assumption declaration that remains. Do not describe it vaguely as
  "technical details".
- Distinguish certificate interfaces from certificate assumptions. A
  paper-local certificate/interface structure is just a formal proof boundary:
  it is an **assumption** only when the paper-facing theorem still takes an
  inhabitant or hypothesis as an explicit input. It is **discharged** when the
  paper folder constructs the witness/certificate and the final paper-facing
  wrapper applies it internally. README/DAG status must say which case holds.
  Auxiliary explicit-input variants are fine, but they must not make the source
  theorem look closed unless there is also a closed wrapper that no longer
  exposes those inputs.
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
  different route. When creating or updating a final validation report, also
  update the front repository `README.md` paper-status table and
  `docs/ECONCSLEAN_CURRENT_STATUS.md` so the public entry points match the
  paper-local verdict.
- For paper-specific status questions, the paper folder `README.md`,
  `DependencyDAG.tex`, paper-facing theorem files, and current targeted Lean
  build are the source of truth. Older author-wide notes or campaign reports
  are historical/secondary and may be stale; never use them to override a
  paper-local README/DAG plus successful build.
- **Post-paper audit protocol:** Before claiming that a paper is done, create
  or update a paper-local final audit. Do this even if a README, DAG, report,
  or successful build already exists; those artifacts are not a substitute for
  the importable audit ledger. The audit must check all four artifacts:
  the cached paper text/PDF, `README.md`, `DependencyDAG.tex`, and the
  paper-facing Lean file(s).
  - Source check: search the cached text for every named paper `Definition`,
    `Lemma`, `Proposition`, `Theorem`, and `Corollary` using a concrete search
    such as `rg -n "THEOREM|Theorem|LEMMA|Lemma|COROLLARY|Corollary|PROPOSITION|Proposition|DEFINITION|Definition" <cached-text>`.
    List the source line or section in the audit report, and say explicitly if
    no numbered definitions/propositions were found.
  - README check: every named source item must have a row using the controlled
    status vocabulary from `docs/STATUS.md`, and every non-`formalized` row must
    name the exact remaining declaration, certificate, or reason for deferral.
  - DAG check: every named result node must have a style consistent with the
    README row. Solid arrows mean verified Lean dependencies; dashed arrows
    mean paper-route/context links or unresolved dependencies. A green node with
    a dashed incoming edge is allowed only if the README/audit says the dashed
    edge is not required by the formal proof.
  - Lean check: create a compiling `PostPaperAudit.lean` or equivalent ledger
    in the paper folder. It must be importable from the paper root module and
    expose one source-numbered audit theorem per final paper endpoint. Prefer
    raw assumption lists in the audit theorem signatures; if a paper-model
    structure is used, the docstring must state the exact paper convention that
    the structure packages. The theorem body should be a thin call to the
    paper-facing declaration, so a human can verify the endpoint in one file.
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
    name them explicitly in the README/DAG.
  - Report check: create or update `FINAL_VALIDATION_REPORT.md` in the paper
    folder. It must state whether the paper is verified, the exact source
    version, the named-result inventory, any deliberate model conventions or
    proof-route deviations, the commands run, and links to the README, DAG, and
    audit ledger.
  - Build check: after updating the audit, run the targeted paper build and
    render the DAG from the paper folder. Also run a placeholder grep over the
    claimed paper and library files, a stale-status grep over the README/DAG/
    final report, and `git diff --check`. Do not mark the audit complete until
    all required commands succeed.
- **Post-verification library extraction pass:** Once a paper theorem closes,
  scan the proof for reusable primitives that belong in `EconCSLib` rather than
  the paper namespace. Good candidates include model-neutral definitions,
  algorithm trace APIs, invariants, side-symmetry lemmas, finite-cardinality
  bridges, and monotonicity/termination facts. Move stable reusable APIs before
  final validation when the extraction is local and low-risk. If the extraction
  would require a broader naming/API design pass, leave the paper-facing wrapper
  in place and record concrete migration candidates in the final report.
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
- Before saying a paper is "done" or "fully verified," perform a paper-local
  validation pass: read the paper README theorem-status rows, inspect the DAG
  status for the named main results, check the paper-facing theorem file for
  the strongest closed wrappers, run the targeted `lake build <module>`, and
  search only the target Lean files for real proof placeholders such as
  `sorry`, `admit`, or `axiom`, for example
  `rg -n "sorry|admit|axiom" papers/<Paper> --glob '*.lean'`. Ignore cached
  PDF text, README prose, skill files, and comments when doing placeholder
  searches; otherwise ordinary instructional text creates false positives.
  If auxiliary certificate/BFS/interface theorems still take explicit inputs,
  verify that the final source wrapper does not expose them before calling the
  source theorem closed.
- After closing a paper seam, run a stale-status grep over the paper README,
  DAG, and final report before committing, for example:
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
  paper README rows and `docs/ECONCSLEAN_CURRENT_STATUS.md` should say which
  algebra, symmetry, probability, or model-integration layers are already closed.
- When stopping or moving papers, document "do not redo" information: closed
  theorem layers, the current endpoint, the next bridge, known traps, and the
  last passing build command. This prevents future agents from spending tokens
  re-deriving the same orientation.
- If the user asks to stop soon, first pick a named theorem/lemma endpoint that
  can be made green quickly, finish that wrapper, and run the targeted module
  plus paper-root builds. Only then update the README/DAG/skill handoff. Do not
  start a fresh hard proof branch just before documenting a handoff.

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
   analogue first if the paper theorem is genuinely continuous, stochastic, or
   measure-theoretic and the direct source statement is shorter, more faithful,
   or necessary to finish the paper. In that case, state the continuous objects
   directly: measures, Bochner or Lebesgue integrals, almost-everywhere claims,
   densities, stopping/renewal assumptions, CTMC transition probabilities, and
   long-run reward limits should be first-class Lean targets rather than
   deferred prose. For proof-specific tactics such as LP certificates,
   continuous-density bridges, RUM support witnesses, symmetric recommendation
   pivots, renewal-reward reductions, CTMC bridges, or ranking/Mallows algebra,
   load the relevant reference in Component 2 instead of putting those
   techniques in this main workflow file.
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
   If Lean exposes that a paper lemma is false as stated, do not silently weaken
   the paper-facing declaration to make progress. State the paper version, prove
   the strongest true nearby lemma separately, and add a small compiled
   counterexample theorem when possible. Mark the README/status row as a
   validation issue with the exact failed hypothesis or inequality.

7. Document exact theorem seams.
   When stopping mid-proof, record the module, theorem, assumptions still
   missing, commands run, the next lemma to prove, and any closed layers that
   should not be revisited. Future agents should not have to rediscover the
   proof state. If a paper is plausibly beyond the current model's effective
   proof-search capacity, make that explicit in the paper README and handoff:
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
- Always scope your git operations (e.g., `git checkout <specific_file>`, `git restore <specific_file>`) strictly to the files you are actively modifying.
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
lake build UserItemFairness.MainTheorems >/tmp/econcs-build.log 2>&1
status=$?
tail -80 /tmp/econcs-build.log
exit $status
```

- Prefer `lake build <touched-root-module>` over full `lake build` until the
  paper slice is ready for integration.
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

Before declaring a paper or proof phase "done," run a final human-facing
validation pass:

- Re-read the paper-facing theorem ledger file (for example,
  `PaperInterface.lean` or the named human-facing theorem file) and check
  each named definition/theorem/corollary against the paper statement.
- Run the paper-local review workflow from within the paper folder:
  `./review-dashboard.sh` and record checks/note any uncertain matches in the
  dashboard before finalizing. If you changed interface statements after earlier
  checks, the launcher surfaces stale warnings so you can refresh only the affected
  items. Use `./review-dashboard.sh --check` to run the precheck step in CI-like,
  non-interactive mode before handoff.
- Confirm every final paper-facing declaration is fully formalized with no
  hidden placeholders; no unresolved `sorry`, scaffold wrappers, or unnamed
  gaps should remain in the claimed result chain.
- If a result remains conditional, ensure assumptions/certificates are explicit
  in both the theorem statement and the paper README status table, with exact
  declaration names and no vague wording.
- Produce a final human-facing report in the paper folder alongside the DAG
  artifacts (TikZ source and rendered image). This report is not for routine
  handoff or an implementation inventory. It is the concise final assessment a
  human should read to decide whether the paper's definitions and named theorem
  statements were represented correctly.
- Before writing that report, do a statement-surface pass outside Lean: list
  every paper definition/object and every named result in source order, decide
  which Lean declaration should be the reader-facing statement for each one,
  and note any source imprecision or proof deviation. Keep this plan current as
  proof work progresses; do not wait until the end to reconstruct the theorem
  inventory from helper lemmas.
- For completed papers, create a compact human-facing Lean interface file when
  the existing theorem files are too implementation-heavy to inspect directly.
  Prefer the name `PaperInterface.lean`. This file should mirror the DAG:
  paper definitions first, with the actual formulas visible in the file, then
  direct theorem statements matching the paper. It must not be only an alias
  list, witness tuple, or pointer layer to `MainTheorems.lean`; a human should
  be able to read this file alone and check that the encoded definitions and
  theorem statements reflect the source text. Proofs may be short calls into
  the implementation layer. Keep exhaustive aliases and auxiliary seams in
  `PostPaperAudit.lean`, not in the interface.
- In `PaperInterface.lean`, aim for one declaration per paper definition or
  formatted paper object, and one declaration per named result or numbered part
  of a named result. If a theorem box has parts (i)--(iii), separate direct
  declarations are acceptable when they mirror those source parts and avoid
  noisy tuple witnesses.
- Treat `PostPaperAudit.lean` as the exhaustive importable ledger, not the
  readable paper interface. Its header should say that explicitly and point to
  `PaperInterface.lean` for the DAG-shaped human-facing surface. It should
  contain source-numbered theorem aliases, named-result wrappers, and supporting
  proof-seam endpoints when those seams are useful for auditing the named
  claims. Do not add standalone proof-facing formula aliases when the formulas
  already appear in `PaperInterface.lean` or are only internal implementation
  plumbing.
- For papers already marked `Verified in Lean`, `Formalized`, or `Formalized
  with caveat`, backfill the same post-paper surface instead of leaving older
  validation artifacts in place: a readable Lean interface (prefer
  `PaperInterface.lean`, or a clearly documented equivalent), an exhaustive
  `PostPaperAudit.lean` endpoint ledger when useful, a compact final validation
  report, and synchronized README/status-table text.
- Confirm the paper root module imports the post-paper audit ledger and that the
  audit ledger has one source-numbered theorem alias or wrapper for each final
  named endpoint.
- Run `python3 scripts/audit_repository.py` after post-paper cleanup. Treat its
  PaperInterface/PostPaperAudit findings as part of the final audit: no tuple
  witness interfaces, no standalone proof-facing formula aliases in the audit
  ledger, no stale `Lean witness` report language, and no completed-paper status
  rows that hide caveats in prose.
- Update the front repository `README.md` paper-status table and
  `docs/ECONCSLEAN_CURRENT_STATUS.md` at the same time, using the exact caveats
  from the final report. Do not let the front README keep stale "partial" or
  "active" wording after a paper-local validation report says a paper is
  verified.
- Use one status vocabulary per artifact. For paper validation reports, prefer
  `complete`, `conditionally complete`, and `incomplete`. For author-wide
  inventory tables, prefer `Complete`, `Partial`, and `Deferred`. Do not mix
  "Verified in Lean" and "Formalized" as parallel category names; use those only
  as descriptive prose if needed.
- **CRITICAL MANDATE: Never lie by omission.** Your validation report MUST list all major theorems, propositions, and sections from the paper. If a result or section was deferred, skipped, or is otherwise unformalized, you MUST list it in the report, mark its status as `not formalized`, and explain why it was deferred. Always be honest and complete regarding the paper's contents.
- The report must first present the paper interface: the definitions and
  formatted mathematical objects the reader needs to inspect, even when the
  source did not number them as "Definition." Examples include bias, aggregate
  posterior, calibration, objective functions, equilibrium notions, allocation
  rules, or any paper-specific named/boxed notation. Give each definition in
  paper notation plus the Lean declarations that encode it.
- Then state each named theorem/proposition/corollary once, matching the paper
  text at theorem-box granularity. Do not expand one source theorem into dozens
  of auxiliary lemmas in the human report. Put only the direct Lean interface
  statement declarations under each theorem, ideally from `PaperInterface.lean`.
  Keep auxiliary implementation inventories in the Lean audit ledger, README,
  or proof files.
- The report must summarize: source version checked, named-result completion
  status (including unformalized items), additional assumptions introduced
  beyond the paper, proof-strategy deviations from the paper, and any suspected
  paper errors or inconsistencies found during formalization.
- If no extra assumptions, deviations, or errors were needed/found, state that explicitly in the report rather than leaving sections implicit.
- Keep the report human-facing. Do not include routine shell commands such as
  `rg -n ...` scans or full build command blocks unless the exact invocation is
  essential to understanding a caveat. Summarize verification checks in prose
  instead. If the report is getting long because it lists every helper theorem,
  stop and replace that section by a short paper-definition/theorem interface
  plus links or declaration names for the main witnesses.
- Avoid wide Markdown tables for definition inventories when the notation or
  declaration names are long. Use a concise bullet checklist instead, with the
  paper notation first and the Lean interface declaration second.

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

## 2. Paper Definitions Checked
These are the mathematical objects from the paper interface. All should be
exposed in `PaperInterface.lean`.

- <Paper object>: <paper notation and one-line statement>.
  Lean: `<PaperInterface.definitionName>`.
- <Next paper object>: <paper notation and one-line statement>.
  Lean: `<PaperInterface.definitionName>`.

## 3. Named Theorem Statements Checked
### Theorem <n>
**Paper statement.** <one theorem-box-level statement matching the source>

**Lean interface statement(s).**
- `<PaperInterface.theoremN_part>`: <which paper clause it states>

**Status.** <formalized / conditional / not formalized>. <1-4 lines of caveats only if needed.>

## 4. Additional Assumptions Beyond Paper
- `<assumption declaration>`: <why needed, where used>
- If none: `None`

## 5. Proof-Strategy Deviations
- `<paper result/declaration>`: <what changed in strategy and why>
- If none: `None`

## 6. Conditional Results and Remaining Gaps
- `<paper item>`: <exact remaining certificate/assumption declaration name>
- If none: `None`

## 7. Suspected Paper Errors or Inconsistencies
- `<location in paper>`: <issue description + Lean/formalization evidence>
- If none: `None`

## 8. Verification Checks
- <build/audit/DAG/no-placeholder outcomes in prose>

## 9. Final Verdict
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
| `EconCSLib/Foundations/Probability/*`, finite PMFs, Markov kernels/chains, concentration, measure inequalities, continuous densities, RUM/noise laws, order statistics, large deviations | `references/proof-foundations-probability.md` |
| `EconCSLib/Foundations/Optimization/*`, argmax/existence/objective wrappers | `references/proof-foundations-optimization.md` |
| `EconCSLib/Applications/RecommenderSystems/*`, accuracy/diversity, producer fairness, count allocation | `references/proof-recommender-systems.md` |
| `EconCSLib/Algorithms/Online/*`, AdWords/MSVV, online matching, regret/Yao | `references/proof-algorithms-online.md` |
| `EconCSLib/MechanismDesign/Auctions/*`, digital goods, GSP, combinatorial auctions | `references/proof-mechanism-design.md` |
| `EconCSLib/Markets/*` or `EconCSLib/SocialChoice/*`, matching, fair division, rankings/Mallows | `references/proof-markets-social-choice.md` |

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
