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
probability support, and finite Markov kernel/chain primitives. Dynamic platform
or surge-pricing papers should usually start with
`EconCSLib.Foundations.Probability.MarkovChain` before introducing
paper-specific states and policies.

## Paper Folders

Each paper folder is an audit artifact for one source paper. The folder name
must use the citation-style convention
`[AuthorInitials][2DigitYear][Descriptor]`, for example

Every paper folder should contain:

- `.gitignore`
- `README.md`
- `DependencyDAG.tex`
- `MainTheorems.lean`
- a locally cached source PDF, ignored by Git
- a locally cached `pdftotext` extraction, kept beside the PDF when licensing
  permits

The paper folder should expose the source's definitions, theorem numbers, and
assumptions clearly enough that a human can compare Lean against the PDF without
reading the entire implementation stack.

## Paper-Facing Ledgers

`MainTheorems.lean` is the stable human-facing interface for a paper. Large
projects may also add `PaperFacingTheorems.lean`, but there should still be one
obvious file that imports the proof files and exposes the paper-level claims.

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
