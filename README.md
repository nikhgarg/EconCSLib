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
| [GS62 College Admissions](papers/GS62CollegeAdmissions) | Formalized | 0/7 | OK: 116 lines | This only uses a few lines of code as its infrastructure has largely been elevated to the shared matching library. |
| [Roth82 Stable Matching](papers/Roth82StableMatching) | Formalized | 0/29 | OK: 490 lines |  |
| [GHW01 Digital Goods](papers/GHW01DigitalGoods) | Formalized | 0/30 | OK: 326 lines | Formalizes the SODA paper; Theorem 8.2 uses the refined monotone-auction wording from the journal version [Goldberg-Hartline-Karlin-Saks-Wright 2006](https://www.sciencedirect.com/science/article/pii/S0899825606000303). |
| [MSVV07 AdWords](papers/MSVV07AdWords) | Formalized | 0/43 | OK: 1015 lines |  |
| [GJ19 Optimal Binary Rating Systems](papers/GJ19OptimalBinaryRatingSystems) | Formalized | 0/56 | Debt: 12481 lines |  |
| [GGSG19 Top Three](papers/GGSG19TopThree) | Formalized | 0/17 | OK: 340 lines |  |
| [GJ18 Informative Rating Systems](papers/GJ18InformativeRatingSystems) | Formalized | 0/15 | OK: 2940 lines |  |
| [LG21 Test Optional Policies](papers/LG21TestOptionalPolicies) | Formalized | 0/23 | OK: 77 lines |  |
| [GN21 Driver Surge Pricing](papers/GN21DriverSurgePricing) | Formalized | 0/36 | OK: 400 lines |  |
| [PRPKG24 Accuracy Diversity](papers/PRPKG24AccuracyDiversity) | Formalized | 0/42 | OK: 287 lines | Proposition 2's printed finite bound appears to miss a factor of 2; Lean proves the corrected finite bound, which is sufficient for the asymptotic 1/2-homogeneity result. |
| [GCG24 User Item Fairness](papers/GCG24UserItemFairness) | Formalized | 0/48 | OK: 387 lines |  |
| [PKG25 No Free Lunch](papers/PKG25NoFreeLunch) | Formalized | 0/15 | OK: 163 lines |  |
| [DSWG24 Discretization Bias](papers/DSWG24DiscretizationBias) | Formalized | 0/41 | OK: 456 lines |  |
| [MBJG25 Producer Fairness](papers/MBJG25ProducerFairness) | Formalized | 10/27 | OK: 332 lines | Additional assumption recorded in the validation report: strict variance decrease is stated with 0 < q_v < 1. |
| [DGD26 Admissions Predictability](papers/DGD26AdmissionsPredictability) | Formalized | 0/101 | OK: 1388 lines | Finite choice-function instability, q-representative and sequential variability, tight-instability constructions, append/remove variability, and linear-assignment variability results are formalized; empirical NYC performance plots are out of theorem scope. |
| [GGRS26 Combatting Gerrymandering RCV](papers/GGRS26CombattingGerrymanderingRCV) | Formalized | 0/19 | OK: 403 lines |  |
| [LOS02 Combinatorial Auctions](papers/LOS02CombinatorialAuctions) | Partially formalized | 0/39 | OK: 371 lines | Greedy approximation, truthfulness, and Theorem 6.1 reductions are formalized. Full formalization requires computational complexity results that are out of scope. |
| [LMMS04 Fair Division](papers/LMMS04FairDivision) | Partially formalized | 0/48 | OK: 303 lines | Sections 2 and 4 are fully formalized. Section 3 has query/descent/rounded-search support. The PTAS/FPTAS runtime layer needs reusable fixed-dimension IP complexity infrastructure. |
| [GKGMM19 Iterative Local Voting](papers/GKGMM19IterativeLocalVoting) | Partially formalized | 0/47 | OK: 2772 lines | Full formalization requires proving stochastic subgradient descent convergence. Theorem 3 is proved as a constrained alternative in general and as the original statement under the explicit full-space condition. |
| [LBG24 Spatial Underreporting](papers/LBG24SpatialUnderreporting) | Partially formalized | 0/27 | OK: 8658 lines | Full formalization requires a homogeneous Poisson process and stopping time derivation |
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

For a concise prompt template, see
[`docs/paper-formalization-quickstart/README.md`](docs/paper-formalization-quickstart/README.md).

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
- [docs/PRIVATE_DEVELOPMENT_WORKFLOW.md](docs/PRIVATE_DEVELOPMENT_WORKFLOW.md): private development and public PR workflow.
- [docs/LEAN_STYLE.md](docs/LEAN_STYLE.md) and [docs/STATUS.md](docs/STATUS.md): contribution conventions.
- [ROADMAP.md](ROADMAP.md): high-level project roadmap.
