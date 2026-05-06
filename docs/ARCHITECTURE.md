# EconCSLib Architecture

This repository has two jobs:

1. `EconCSLib/` is the reusable textbook layer.
2. `papers/` is the paper-by-paper audit trail.

The split is deliberately strict. Generic concepts that should be reusable
across EC papers belong in `EconCSLib`; source-faithful theorem statements,
paper notation, PDFs, DAGs, and status ledgers belong in `papers/`.

## Core Library

`EconCSLib/` contains abstract definitions and theorems with paper-specific
notation removed. A result belongs here when a second paper would plausibly use
it after renaming variables.

Current top-level areas:

- `Foundations/`: finite math, graph/counting tools, probability, econometrics,
  optimization, asymptotics, and reusable proof infrastructure.
- `MechanismDesign/`: auctions and mechanism primitives.
- `SocialChoice/`: fair division and voting-style primitives.
- `Markets/`: matching and platform/market primitives.
- `Learning/`: bandits and learning models.
- `Algorithms/`: online algorithms, complexity, and algorithmic proof tools.
- `Applications/`: domain-specific reusable layers, currently including
  recommender-system policy/allocation abstractions.

Probability foundations currently include finite PMFs and expectations,
conditional probability, finite variance, measure inequalities, continuous
probability support, finite Markov kernel/chain primitives, two-state CTMC
closed-form support, finite occupancy processes, and finite MDP primitives, plus finite
stochastic-dominance/coupling certificates and an algebraic Gaussian
posterior/CDF interface. GLM/LG-style testing papers should start with
`EconCSLib.Foundations.Probability.Gaussian` for conjugate posterior formulas,
standardization, finite multi-signal weights, nonzero-noise-mean signal
centering, posterior/raw-signal threshold conversion, posterior and threshold
monotonicity, finite-mixture capacity/admitted-mean accounting, and explicit
CDF/hazard assumptions before introducing paper-specific admissions thresholds.
Dynamic platform or surge-pricing papers should usually start with
`EconCSLib.Foundations.Probability.MDP` for controlled dynamics,
`EconCSLib.Foundations.Probability.MarkovChain` for passive dynamics, and
`EconCSLib.Foundations.Probability.CTMC` for continuous-time two-state switch
probabilities, before introducing paper-specific states and policies. Use
`EconCSLib.Foundations.Probability.StochasticDominance` for monotone policy or
state-distribution comparisons. Rating-system and recommender asymptotic papers
with finite rating scales should start from
`EconCSLib.Foundations.Probability.FiniteSupportMGF` for log-MGF/rate-function
algebra and `EconCSLib.Foundations.Probability.LargeDeviations` for
exponential-rate certificates, finite union/weighted-sum aggregation,
upper/lower exponential bound weakening, and pairwise ranking-error bounds. The
analytic Cramer/Gartner-Ellis or
Laplace-principle proof can remain as a distribution-family certificate until
the paper needs that theorem internally. Accuracy-diversity papers with
continuous top-`k` values should use
`EconCSLib.Foundations.Probability.OrderStatistics` for top-`k` expectation
oracles and scaled marginal-limit certificates, then feed the resulting
eventual marginal sandwiches into the optimization layer. Real-valued threshold
or tail arguments should use
`EconCSLib.Foundations.Probability.RealDistribution` for lower CDF mass,
upper-tail mass, monotonicity, and complement identities before adding
paper-specific distribution-family asymptotics.

Optimization foundations currently include finite pointwise argmax/existence
lemmas, abstract expected-objective wrappers, feasible-set optimality
certificates, finite feasible-search wrappers, move-graph exchange optimality,
and lightweight finite LP weak-duality certificates. Papers with LP witnesses,
exchange arguments, threshold searches, or endpoint/current-bound optimality
proofs should start with
`EconCSLib.Foundations.Optimization`; the longer promotion plan lives in
[`docs/OPTIMIZATION_LIBRARY_ROADMAP.md`](OPTIMIZATION_LIBRARY_ROADMAP.md).

## Library Maintenance TODOs

- Deferred until the active auction paper finishes: remove the broad
  `EconCSLib.MechanismDesign.Auctions.MainTheorems` import from
  `EconCSLib.Basic` and keep paper-facing auction theorem aggregators imported
  directly by paper modules. Current Lake builds can materialize only hash files
  for that heavy aggregate during dependent paper builds, then fail later
  imports looking for the `.olean`/`.ilean` artifacts. The preferred fix is an
  import-boundary cleanup, not paper-theorem rewrites.
- Active auction cleanup note: do not repair
  `EconCSLib.MechanismDesign.Auctions.MainTheorems` opportunistically while the
  auction formalization is being edited elsewhere. As of the probability-library
  cleanup pass, full `lake build EconCSLib` can be blocked by auction-local
  theorem-name drift, for example the missing
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_completion_certificate_of_ex_post`
  reference near `MainTheorems.lean:28022`. Keep validating unrelated work with
  narrower targets such as `lake build EconCSLib.Foundations` until the auction
  thread stabilizes, then do the import-boundary cleanup above.

## Paper Folders

Each paper folder is an audit artifact for one source paper. The folder name
must use the citation-style convention
`[AuthorInitials][2DigitYear][Descriptor]`, for example

Every paper folder should contain:

- `.gitignore`
- `README.md`
- `DependencyDAG.tex`
- `FORMALIZATION_PLAN.md`
- `MainTheorems.lean`
- `PaperInterface.lean`
- a locally cached source PDF, ignored by Git
- a locally cached `pdftotext` extraction, kept beside the PDF when licensing
  permits

The paper folder should expose the source's definitions, theorem numbers, and
assumptions clearly enough that a human can compare Lean against the PDF without
reading the entire implementation stack.

For agent-facing instructions on starting and finishing a paper, use
[`docs/AGENT_FORMALIZATION_WORKFLOW.md`](AGENT_FORMALIZATION_WORKFLOW.md). For a
concise domain-by-domain index of reusable modules and entrypoints, use
[`docs/ECONCSLIB_DOMAIN_INDEX.md`](ECONCSLIB_DOMAIN_INDEX.md).

## Lean Style

Follow the Mathlib-derived conventions in `docs/LEAN_STYLE.md`: narrow imports,
`UpperCamelCase.lean` module names, module docstrings with main declarations
for reusable library files, and Mathlib-style declaration names. Paper-facing
wrappers may preserve source theorem numbers for auditability, but generic
`EconCSLib` APIs should use paper-independent names.

## Paper-Facing Ledgers

`PaperInterface.lean` is the stable human-facing interface for a completed or
formalized paper. It should be readable on its own: expose the source formulas
and theorem statements in a compact DAG-shaped order, with short proofs that
call into `MainTheorems.lean` or lower proof files. `MainTheorems.lean` remains
the implementation-level wrapper layer for source-faithful theorem endpoints.

Paper-facing ledgers should:

- state definitions and theorem wrappers in source order;
- use paper theorem/lemma/proposition names or numbers in docstrings;
- expose exact formulas with paper-local `def` or `abbrev`s when generic
  library names would hide the source equation;
- make conditional assumptions explicit in theorem signatures;
- keep source-faithful wrappers separate from auxiliary finite analogues or
  certificate interfaces;
- avoid `#check`-only ledgers and hidden proof placeholders.

A `formalized` README row should point to a real Lean declaration and should
list `None` under remaining assumptions. Conditional rows must name the exact
open certificate, bridge, or assumption declaration.

Paper README status cells use the controlled vocabulary in `docs/STATUS.md`.
Do not put free-form progress prose in the status cell; put caveats, closed
sub-results, and remaining certificates in the final ledger column.

## Upstreaming

The normal workflow is:

1. Scaffold the paper folder and paper-facing theorem statements.
2. Build the proof locally, using source notation.
3. Identify reusable seams that pass the second-paper test.
4. Move those seams to `EconCSLib`.
5. Leave thin paper-facing wrappers in `papers/[Paper]/MainTheorems.lean`.

Reusable seams include finite expectation/probability lemmas, Markov kernels,
probability inequalities, allocation primitives, mechanism interfaces,
matching/fair-division facts, optimization certificates, and generic algorithm
invariants. Hyper-specific algebraic rearrangements should stay paper-local.

## Automation Direction

The intended agent workflow is: given a paper link, cache the source, extract
text, enumerate named results, create the DAG and theorem ledger, upstream
reusable primitives, and then close the paper-facing wrappers. The
`scripts/new_paper.py` intake script provides the deterministic first step of
that workflow, while `scripts/audit_repository.py` checks mechanical hygiene
before status updates or handoff.
