# EconCSLib

`EconCSLib` is a Lean 4 library dedicated to formalizing results that matter to the Economics and Computation (EC) community. 

The project has three high-level goals:
1. **Formalize canonical EC-style papers:** Systematically verify both foundational Test-of-Time papers and modern, active research.
2. **Extract reusable library primitives:** Build a robust, shared foundation of discrete math, probability, game theory, and mechanism design concepts that the community can reuse.
3. **Develop AI formalization skills:** Eventually turn this structured workflow into an agent skill for autonomously verifying new EC papers.

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
- A `README.md` containing the citation, source URLs, and a theorem-status ledger.
- A `DependencyDAG.tex` providing a visual proof roadmap of how definitions and lemmas connect.
- A `MainTheorems.lean` file containing notation-exact wrappers around the core library's theorems, demonstrating fidelity to the original text.

## Upstreaming Workflow
When formalizing a new paper, authors typically build everything locally in their `papers/` folder. Once a proof is stable, the generalized mathematical core is "upstreamed" to `EconCSLib`, leaving only the thin, paper-facing wrappers behind.

## Orientation
To get started or review the current formalization roadmap, see the documentation:
- [docs/EC_TEST_OF_TIME_FORMALIZATION_PLAN.md](docs/EC_TEST_OF_TIME_FORMALIZATION_PLAN.md)
- [docs/ECONCSLEAN_CURRENT_STATUS.md](docs/ECONCSLEAN_CURRENT_STATUS.md)
- [docs/PAPER_MAP.md](docs/PAPER_MAP.md)

- [skills/econcs-formalizer/SKILL.md](skills/econcs-formalizer/SKILL.md)

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
