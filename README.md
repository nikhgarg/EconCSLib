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

Paper status changes frequently. Each paper folder has a paper-local
`status.json`; the generated human-facing snapshot is
[`papers/human_status.json`](papers/human_status.json), and the generated
markdown/site tables are [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md) and
[`site/index.html`](site/index.html).

Paper IDs and folder names are stable artifact identifiers and may track an
arXiv, conference, or original working-paper year. Public status tables use the
published citation title and year.

<!-- BEGIN GENERATED PAPER STATUS TABLE -->
| Paper | Status | Review | Interface | Human summary |
|---|---:|---:|---:|---|
| [GS62 College Admissions](papers/GS62CollegeAdmissions) | Formalized | 0/7 | OK: 109 lines | This only uses a few lines of code as its infrastructure has largely been elevated to the shared matching library. |
| [Roth82 Stable Matching](papers/Roth82StableMatching) | Formalized | 0/27 | OK: 468 lines |  |
| [GHW01 Digital Goods](papers/GHW01DigitalGoods) | Formalized | 0/19 | OK: 290 lines | The journal version is used as the corrected source for Theorem 8.2 [Goldberg et al. 2006](https://www.sciencedirect.com/science/article/pii/S0899825606000303). |
| [MSVV07 AdWords](papers/MSVV07AdWords) | Formalized | 0/39 | OK: 613 lines |  |
| [LG21 Test Optional Policies](papers/LG21TestOptionalPolicies) | Formalized | 0/16 | OK: 76 lines |  |
| [GN21 Driver Surge Pricing](papers/GN21DriverSurgePricing) | Formalized | 0/24 | OK: 160 lines |  |
| [GCG24 User Item Fairness](papers/GCG24UserItemFairness) | Formalized | 0/18 | OK: 235 lines |  |
| [DSWG24 Discretization Bias](papers/DSWG24DiscretizationBias) | Formalized | 0/32 | OK: 406 lines |  |
| [MBJG25 Producer Fairness](papers/MBJG25ProducerFairness) | Formalized | 0/17 | OK: 296 lines | Formalization required an additional assumption that Bernoulli success probability was strictly bounded away from 0 and 1. |
| [LOS02 Combinatorial Auctions](papers/LOS02CombinatorialAuctions) | Partially formalized | 0/30 | OK: 174 lines | Greedy approximation, truthfulness, and Theorem 6.1 reductions are closed; machine-level complexity remains external. |
| [LMMS04 Fair Division](papers/LMMS04FairDivision) | Partially formalized | 0/33 | OK: 171 lines | Sections 2 and 4 are closed; Section 3 has query/descent/rounded-search support. The PTAS/FPTAS runtime layer needs reusable fixed-dimension IP complexity infrastructure. |
| [PRPKG24 Accuracy Diversity](papers/PRPKG24AccuracyDiversity) | Partially formalized | 0/27 | OK: 138 lines | Proposition 2's printed finite bound appears to miss a factor of 2; Lean proves the corrected finite bound, which is sufficient for the asymptotic 1/2-homogeneity result. Fully formalizing the remaining result, Proposition 4, requires a general Laplace-principle-related analysis library. |
<!-- END GENERATED PAPER STATUS TABLE -->

For more detail, use:

- `papers/<PaperName>/status.json` for the paper-local source of truth.
- [`papers/human_status.json`](papers/human_status.json) for the compact
  public-facing status summary.
- [`papers/status.json`](papers/status.json) for the generated aggregate
  status, review counts, and interface metadata.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md) for the generated public paper
  status table.
- [`site/index.html`](site/index.html) for the generated public website status
  table.
- Individual `papers/<PaperName>/README.md` files for paper-specific caveats.

Partial public formalizations are included when the remaining assumption seam is
explicit and useful to expose. LMMS04 and LOS02 are the current examples:
LMMS04's final complexity claim is held behind an explicit fixed-dimension IP
runtime boundary, and LOS02's final NP-hardness/`NP = ZPP` consequences are
held behind external machine-level complexity facts.

## Starting A New Paper With An Agent

To get started in formalizing your own paper, clone the repository and open an
LLM agent tool (I use Codex with GPT 5.5 in xhigh thinking mode). Give the
agent the paper link, and ask it to formalize the paper using the skill and
workflow in the repository. (And please let me know what your experience is
like).

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

## License

Unless otherwise noted, the Lean source, scripts, documentation, and site source
are licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE).
Source-paper PDFs and extracted text caches are not included in the public
repository unless redistribution rights have been checked separately.

## More Documentation

- [docs/README.md](docs/README.md): documentation index.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): library modules by domain.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
