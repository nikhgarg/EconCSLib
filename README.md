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

Paper status changes frequently. This table is a human-readable snapshot.
Each paper folder has a paper-local `status.json`; the aggregate
[`papers/status.json`](papers/status.json) is generated from those files.

| Paper | Status | Review | Interface | Human summary |
|---|---|---:|---|---|
| [DSWG24 Discretization Bias](papers/DSWG24DiscretizationBias) | Formalized | 0/32 | OK: 406 lines | Main discretization-bias theorems are closed; proof-route deviations are recorded. |
| [GHW01 Digital Goods](papers/GHW01DigitalGoods) | Formalized | 0/19 | OK: 290 lines | Journal Theorem 8.2 and source-convention Theorem 9.3 are closed. |
| [GCG24 User-Item Fairness](papers/GCG24UserItemFairness) | Formalized | 0/18 | OK: 235 lines | Recommendation fairness propositions and theorem statements are closed. |
| [Roth82 Stable Matching](papers/Roth82StableMatching) | Formalized | 0/27 | OK: 468 lines | Named matching results are closed on Roth's strict marriage domain. |
| [GS62 College Admissions](papers/GS62CollegeAdmissions) | Formalized | 0/7 | OK: 109 lines | Stable-marriage and college-admissions results are closed; OCR is only a source-audit note. |
| [MBJG25 Producer Fairness](papers/MBJG25ProducerFairness) | Formalized with caveat | 0/17 | OK: 296 lines | Bayesian rating-system results are formalized with a documented boundary correction. |
| [MSVV07 AdWords](papers/MSVV07AdWords) | Formalized | 0/39 | OK: 613 lines | Core AdWords, Theorems 8--9, and Section 6/8 extensions are closed. |
| [LG21 Test-Optional Policies](papers/LG21TestOptionalPolicies) | Formalized | 0/16 | OK: 92 lines | Named definitions and Section 3--4 results are closed under paper-facing source models. |
| [GN21 Driver Surge Pricing](papers/GN21DriverSurgePricing) | Formalized | 0/24 | OK: 184 lines | CTMC lemmas and Theorems 1--4 are exposed. |
| [LMMS04 Fair Division](papers/LMMS04FairDivision) | Partially formalized | 0/33 | OK: 171 lines | Sections 2 and 4 are formalized; final PTAS/FPTAS runtime remains external. |
| [LOS02 Combinatorial Auctions](papers/LOS02CombinatorialAuctions) | Partially formalized | 0/30 | OK: 174 lines | Auction and truthfulness endpoints are formalized; machine-level complexity remains external. |

For more detail, use:

- `papers/<PaperName>/status.json` for the paper-local source of truth.
- [`papers/status.json`](papers/status.json) for the generated aggregate
  status, review counts, and interface metadata.
- [docs/PAPER_STATUS.md](docs/PAPER_STATUS.md) for paper citation, build
  target, status, caveat, and review entrypoint.
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
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
