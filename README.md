# EconCSLib

`EconCSLib` is a Lean 4 library dedicated to formalizing results that matter to the Economics and Computation (EC) community. 

The project has three high-level goals:
1. **Formalize canonical EC-style papers:** Systematically verify both foundational Test-of-Time papers and modern, active research.
2. **Extract reusable library primitives:** Build a robust, shared foundation of discrete math, probability, game theory, and mechanism design concepts that the community can reuse.
3. **Develop AI formalization skills:** Eventually turn this structured workflow into an agent skill for autonomously verifying new EC papers.

## Paper Formalization Status

Current paper status is tracked in the table below and in each
`papers/[Paper]/README.md`. PDFs are cached locally in each paper folder and
ignored by Git; extracted `.txt` caches are kept beside them for source audits.

| Paper folder | Paper | Overall status | Current Lean surface |
|---|---|---|---|
| `papers/MBJG25ProducerFairness` | *Balancing Producer Fairness and Efficiency via Bayesian Rating System Design* | Formalized with caveat | Source Theorems 3.1--3.2 are covered, with the strict boundary issue documented. |
| `papers/MSVV07AdWords` | *AdWords and Generalized Online Matching* | Partially formalized | Final finite/family theorem surfaces are strong; source Lemmas 1--7 are not one-for-one wrappers. |
| `papers/DSWG24DiscretizationBias` | *Addressing Discretization-Induced Bias in Demographic Prediction* | Partially formalized | Source-facing expected-objective wrappers cover Theorem 2(i)--(ii); Theorem 1 and Theorem 2(iii) remain open. |
| `papers/Roth82StableMatching` | *The Economics of Matching: Stability and Incentives* | Partially formalized | Conditional DA wrappers cover Theorems 1, 2, and 5 seams; impossibility and manipulation theorems remain open. |
| `papers/GHW01DigitalGoods` | *Competitive Auctions and Digital Goods* | Partially formalized | Digital-goods primitives, fixed-price support, and RSOP skeleton are formalized; approximation/lower bounds are open. |
| `papers/GCG24UserItemFairness` | *The User-Item Fairness Tradeoff in Recommender Systems* | Partially formalized | Active work by another agent; not audited in this cleanup pass. |

## Repository Architecture: Textbook vs. Audit Trail

This repository strictly separates generalized mathematical foundations from paper-specific proofs using a "Textbook vs. Audit Trail" model:

### 1. The Core Library (`EconCSLib/`)
This is the "Textbook." It contains highly abstracted, generic EC/CS/econ definitions and theorems stripped of paper-specific notation. If a concept is foundational enough that a graduate student should know it (e.g., Gale-Shapley, Nash equilibrium, LP duality, or generic choice models), it belongs here.

The core library is organized around major EC domains:
- `Foundations/`: Discrete math, probability, asymptotics, and econometrics.
- `MechanismDesign/`: Auctions, contracts, and information design.
- `SocialChoice/`: Fair division and voting.
- `Markets/`: Matching and platform design.
- `Learning/`: Bandits and learning in games.
- `Algorithms/`: Online algorithms and complexity.
- `Applications/`: Recommender systems and other applied models.

### 2. Paper Formalizations (`papers/`)
This is the "Audit Trail." Each paper formalized in this repository gets its own isolated folder named using the `[AuthorInitials][2DigitYear][Descriptor]` format (e.g., `MSVV07AdWords`).

These folders serve to prove that the *specific claims in a specific PDF* are true. 
Each paper folder strictly adheres to a standard template:
- A downloaded `.pdf` of the source material (git-ignored to prevent repo bloat).
- A cached `.txt` extraction created once with `pdftotext` for named-statement
  audits.
- A `README.md` containing the citation, source URLs, and a theorem-status ledger.
- A `DependencyDAG.tex` providing a visual proof roadmap of how definitions and lemmas connect.
- A `MainTheorems.lean` file containing notation-exact wrappers around the core library's theorems, demonstrating fidelity to the original text.

## Upstreaming Workflow
When formalizing a new paper, authors typically build everything locally in their `papers/` folder. Once a proof is stable, the generalized mathematical core is "upstreamed" to `EconCSLib`, leaving only the thin, paper-facing wrappers behind.

## Orientation
For current paper status, start with the table above and the relevant
paper-folder `README.md`. For repository conventions, see:

- [docs/ECONCSLEAN_CURRENT_STATUS.md](docs/ECONCSLEAN_CURRENT_STATUS.md)
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)
- [skills/econcs-formalizer/SKILL.md](skills/econcs-formalizer/SKILL.md)

Historical plans and handoff reports live under `docs/` and `docs/archive/`.

## Build

This code is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

```bash
lake build EconCSLib
```

## GitHub Automation

The repository keeps CI and manual dependency-update workflows under
`.github/workflows`. Release-tag/release-publishing automation has been removed;
releases should be cut manually if needed.

## Repository Direction

The imported decision/fairness/recommendation track is not the whole project.
It is the first substantial batch of paper formalization work inside
`EconCSLib`, and it should inform how the broader library grows.

That broader roadmap lives in [ROADMAP.md](ROADMAP.md).
