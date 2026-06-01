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
markdown table is [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md).

<!-- BEGIN GENERATED PAPER STATUS TABLE -->
| Paper | Status | Review | Interface | Human summary |
|---|---:|---:|---:|---|
| [GS62 College Admissions](papers/GS62CollegeAdmissions) | Formalized | 0/7 | OK: 109 lines | This only uses a few lines of code as its infrastructure has largely been elevated to the shared matching library. |
| [Roth82 Stable Matching](papers/Roth82StableMatching) | Formalized | 0/27 | OK: 468 lines |  |
| [GHW01 Digital Goods](papers/GHW01DigitalGoods) | Formalized | 0/19 | OK: 290 lines | Theorem 8.2 follows the journal version; the broader preliminary wording is documented as refuted. |
| [MSVV07 AdWords](papers/MSVV07AdWords) | Formalized | 0/39 | OK: 613 lines |  |
| [GN21 Driver Surge Pricing](papers/GN21DriverSurgePricing) | Formalized | 0/24 | OK: 184 lines |  |
| [LG21 Test Optional Policies](papers/LG21TestOptionalPolicies) | Formalized | 0/16 | OK: 92 lines |  |
| [DSWG24 Discretization Bias](papers/DSWG24DiscretizationBias) | Formalized | 0/32 | OK: 406 lines |  |
| [GCG24 User Item Fairness](papers/GCG24UserItemFairness) | Formalized | 0/18 | OK: 235 lines |  |
| [MBJG25 Producer Fairness](papers/MBJG25ProducerFairness) | Formalized with caveat | 0/17 | OK: 296 lines | Formalization required an additional assumption that Bernoulli success probability was strictly bounded away from 0 and 1. |
| [LOS02 Combinatorial Auctions](papers/LOS02CombinatorialAuctions) | Partially formalized | 0/30 | OK: 174 lines | Greedy approximation, truthfulness, and Theorem 6.1 reductions are closed; machine-level complexity remains external. |
| [LMMS04 Fair Division](papers/LMMS04FairDivision) | Partially formalized | 0/33 | OK: 171 lines | Sections 2 and 4 are closed; Section 3 has query/descent/rounded-search support. The PTAS/FPTAS runtime layer needs reusable fixed-dimension IP complexity infrastructure. |
| [KR21 Monoculture](papers/KR21Monoculture) | Partially formalized | 0/6 | OK: 82 lines | Continuous RUM endpoints are exposed; arbitrary-size Mallows dominance and remaining paper-scope bridges remain open. |
| [GLM20 Dropping Standardized Testing](papers/GLM20DroppingStandardizedTesting) | Partially formalized | 0/50 | OK: 405 lines | Main early results and selected Section 5 bridge endpoints are exposed; concrete Bayesian-game identifications remain open. |
| [EOS07 GSP](papers/EOS07GSP) | Partially formalized | 0/15 | OK: 75 lines | Non-truthfulness, examples, and finite theorem endpoints are exposed with an explicit completion boundary. |
| [IM05 Marriage Honesty Stability](papers/IM05MarriageHonestyStability) | Partially formalized | 0/6 | OK: 106 lines | Matching preliminaries and theorem wrappers are exposed; algorithmic and experimental constructions remain open. |
| [PRPKG24 Accuracy Diversity](papers/PRPKG24AccuracyDiversity) | Partially formalized | 0/36 | OK: 160 lines | Finite optimization and distribution checkpoints are exposed; general order-statistic certificates remain open. |
<!-- END GENERATED PAPER STATUS TABLE -->

For more detail, use:

- `papers/<PaperName>/status.json` for the paper-local source of truth.
- [`papers/human_status.json`](papers/human_status.json) for the compact
  public-facing status summary.
- [`papers/status.json`](papers/status.json) for the generated aggregate
  status, review counts, and interface metadata.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md) for the generated public paper
  status table.
- Individual `papers/<PaperName>/README.md` files for paper-specific caveats.

Partial public formalizations are included when the remaining assumption seam is
explicit and useful to expose. LMMS04 and LOS02 are the current examples:
LMMS04's final complexity claim is held behind an explicit fixed-dimension IP
runtime boundary, and LOS02's final NP-hardness/`NP = ZPP` consequences are
held behind external machine-level complexity facts.

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

## License

Unless otherwise noted, the Lean source, scripts, documentation, and site source
are licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE).
Source-paper PDFs and text caches remain governed by their own source licenses
or publication terms.

## More Documentation

- [docs/README.md](docs/README.md): documentation index.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md): public paper status.
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): repository architecture.
- [docs/ECONCSLIB_DOMAIN_INDEX.md](docs/ECONCSLIB_DOMAIN_INDEX.md): library modules by domain.
- [docs/PRIVATE_DEVELOPMENT_WORKFLOW.md](docs/PRIVATE_DEVELOPMENT_WORKFLOW.md): private development and public PR workflow.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
