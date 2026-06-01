# EconCSLib

EconCSLib is a Lean 4 project for checking results in Economics and
Computation. The repository has two roles:

- Build a reusable library of mathematical tools for EC: probability,
  optimization, matching, auctions, online algorithms, fair division, learning,
  and related foundations.
- Keep a paper-by-paper audit trail showing which source definitions and
  theorems have been formalized, which assumptions remain, and where the proof
  deviates from an informal paper argument.

The project is meant to support both formalization work and human review. A
human reader should be able to open a completed paper folder and understand
what was proved without reading the full Lean implementation.

## How The Repository Is Organized

- `EconCSLib/` is the reusable library. Code here should be paper-independent
  and useful across more than one formalization.
- `papers/` contains one folder per source paper. These folders preserve the
  paper's notation, theorem numbering, proof DAG, validation report, and
  human-facing Lean interface.
- `docs/` contains project documentation. Some files are human-facing strategy
  and status documents; others are detailed conventions for agents and
  maintainers.
- `skills/econcs-formalizer/` contains the agent workflow instructions used to
  formalize papers consistently.

## Reviewing A Formalized Paper

Start in the paper folder under `papers/<PaperName>/`.

For a completed or nearly completed paper, read these files in this order:

1. `FINAL_VALIDATION_REPORT.md`: source checked, theorem inventory, proof
   deviations, remaining assumptions, and final status.
2. `PaperInterface.lean`: readable definitions and theorem statements matching
   the paper. This is the main human-facing Lean file.
3. Dependency graph: visual map of named definitions, lemmas, theorems, and
   remaining caveats. Some paper folders keep only the source graph tracked and
   render the PDF locally.
4. `README.md`: paper metadata and theorem-status ledger.

Implementation-level proof files are for maintainers and agents. They should
not be necessary for a first human audit of what the paper claims and what Lean
proves.

## Current Status

Paper status changes frequently. This table is a human-readable snapshot; each
paper folder contains the detailed theorem ledger and caveats.

| Paper | Status | Human summary |
|---|---|---|
| [DSWG24 Discretization Bias](papers/DSWG24DiscretizationBias) | Formalized | Main discretization-bias theorems are closed; report documents a proof-route deviation from the paper. |
| [GHW01 Digital Goods](papers/GHW01DigitalGoods) | Partially formalized | Public partial: major auction primitives and several named results are formalized, but Theorems 8.2 and 9.3 still rely on explicit model-certificate assumptions that should be derived or promoted to source assumptions. |
| [GCG24 User-Item Fairness](papers/GCG24UserItemFairness) | Formalized | Recommendation fairness propositions and theorem statements are closed. |
| [Roth82 Stable Matching](papers/Roth82StableMatching) | Formalized | The cached paper's named Theorems 1--7, Lemmas 1--2, and Corollary 5.1 are closed on Roth's stated strict marriage domain without extra model-certificate assumptions. |
| [GS62 College Admissions](papers/GS62CollegeAdmissions) | Formalized | Stable-marriage and finite college-admissions results are closed without extra certificates or conditional proof gaps; the cached PDF scan has poor OCR, recorded as a source-audit note rather than a formalization caveat. |
| [MBJG25 Producer Fairness](papers/MBJG25ProducerFairness) | Formalized with caveat | Bayesian rating-system results are formalized with a documented boundary correction. |
| [MSVV07 AdWords](papers/MSVV07AdWords) | Formalized | Core AdWords, Theorems 8--9, and Section 6/8 extensions are closed, including the source-shaped Section 6 top-`n_q` distinct-bidder page-level guarantee. |
| [LG21 Test-Optional Policies](papers/LG21TestOptionalPolicies) | Formalized | All named definitions and Section 3--4 results are closed under the paper-facing source models; human dashboard review remains external. |
| [GN21 Driver Surge Pricing](papers/GN21DriverSurgePricing) | Formalized | Named CTMC lemmas and Theorems 1-4 are exposed; zero-mass boundary behavior is audited separately. |
| [LMMS04 Fair Division](papers/LMMS04FairDivision) | Partially formalized | Public partial: Sections 2 and 4 are formalized; the final PTAS/FPTAS runtime claim remains behind `ExternalSolverConsequence`. |
| [LOS02 Combinatorial Auctions](papers/LOS02CombinatorialAuctions) | Partially formalized | Public partial: auction, greedy approximation, critical-price, and truthfulness endpoints are formalized; final machine-level complexity consequences remain external. |

For more detail, use:

- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md) for paper citation, build
  target, status, caveat, and review entrypoint.
- Individual `papers/<PaperName>/README.md` files for paper-specific caveats.

Partial public formalizations are included when the remaining assumption seam is
explicit and useful to expose. GHW01, LMMS04, and LOS02 are the current
examples: GHW01 should next discharge model-certificate assumptions for its
digital-goods auction endpoints; LMMS04's final complexity claim is held behind
an explicit fixed-dimension IP runtime boundary; and LOS02's final
NP-hardness/`NP = ZPP` consequences are held behind external machine-level
complexity facts.

## Starting A New Paper With An Agent

Use [docs/AGENT_FORMALIZATION_WORKFLOW.md](docs/AGENT_FORMALIZATION_WORKFLOW.md).
That file is intentionally agent-facing and includes the expected prompts,
artifact checklist, validation commands, and workflow rules.

## Development

This project is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

Useful commands:

```bash
lake build EconCSLib
python3 scripts/audit_repository.py
```

`lake build EconCSLib` is the first fresh-clone check and should pass for the
public repository. `python3 scripts/audit_repository.py` is a maintainer audit.
In a fresh clone it may report missing ignored local artifacts such as source
PDFs, rendered dependency-graph PDFs, or review-dashboard caches; those are not
Lean verification failures.

## Review Theorem Statements

Use the paper-local launcher to validate `PaperInterface.lean` statements:

```bash
papers/DSWG24DiscretizationBias/review-dashboard.sh
```

The dashboard stores reviewer, timestamp, match decision, notes, statement
snapshots, and stale-detection digests under each paper's `.review_traces/`
directory. For the full workflow, CLI checks, exports, and slice conventions,
see [docs/REVIEW_DASHBOARD.md](docs/REVIEW_DASHBOARD.md).

## More Documentation

- [CITATION.cff](CITATION.cff): citation metadata for the public repository.
- [docs/README.md](docs/README.md): documentation index split into
  human-facing and agent-facing references.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture,
  paper-folder contract, and maintenance notes.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): reusable
  library modules by domain.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status, build
  target, and review entrypoint.
- [docs/PROBABILITY_LIBRARY_ROADMAP.md](docs/PROBABILITY_LIBRARY_ROADMAP.md):
  probability-library roadmap.
- [docs/OPTIMIZATION_LIBRARY_ROADMAP.md](docs/OPTIMIZATION_LIBRARY_ROADMAP.md):
  optimization-library roadmap.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md): Lean style conventions.
- [docs/STATUS.md](docs/STATUS.md): controlled vocabulary for paper status.
- [docs/PUBLIC_RELEASE_CHECKLIST.md](docs/PUBLIC_RELEASE_CHECKLIST.md): checks
  before public announcements or broad external contribution requests.
- [docs/REPOSITORY_LAUNCH_PLAN.md](docs/REPOSITORY_LAUNCH_PLAN.md): maintainer
  plan for the public/private split and GitHub Pages activation.
- [docs/PAGES_PUBLISHING.md](docs/PAGES_PUBLISHING.md): static-site publishing
  checklist for the draft GitHub Pages site.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
