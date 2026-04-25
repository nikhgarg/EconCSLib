# EconCSLib Roadmap

## Vision
`EconCSLib` aims to become the standard Lean 4 library for the Economics and Computation (EC) community. By coupling mathematical foundations with rigorous paper formalizations, we are building a verifiable "textbook" of mechanism design, market algorithms, and game theory, alongside an "audit trail" proving the claims of canonical EC literature.

## The Architecture is Set
The repository is no longer a fresh scaffold. We have successfully completed the **"Textbook vs. Audit Trail"** architectural split:
1. **The Textbook (`EconCSLib/`):** Generic, abstracted mathematical and economic primitives.
2. **The Audit Trail (`papers/`):** Isolated, notation-exact formalizations of specific papers, backed by Dependency DAGs and rigorous theorem-status ledgers.

This means our immediate roadmap is no longer about *how* to organize the repository, but *what* to formalize next.

## Phase 1: Completing the "Test of Time" Baseline

Our immediate priority is to finish the formalizations of the historic SIGecom Test-of-Time award papers. These foundational papers stress-test our core library and force us to build the most critical, reusable primitives.

**Active Targets:**
- **Combinatorial Auctions (LOS '02):** Complete the proof that single-minded bidders face truth-telling mechanisms.
- **Fair Division (LMMS '04):** Close the polynomial-time and existence bounds for bounded-envy allocations.
- **AdWords / MSVV (MSVV '07):** Finish the deterministic `(1 - 1/e)` lower bounds and competitive ratio accounting.
- **Digital Goods (GHW '01):** Close the RSOP-style randomized approximation bounds.

## Phase 2: Expanding the 7 Core Pillars of `EconCSLib`

As we formalize papers, we will aggressively upstream reusable math into the 7 pillars of our core library.

1. **Foundations (Math & Probability):** 
   - *Next:* Expand asymptotic limit topologies (required for the continuum limits of Accuracy-Diversity and Monoculture) and continuous probability distributions.
2. **Mechanism Design:** 
   - *Next:* Myerson's Lemma, VCG mechanisms, and Revenue Equivalence.
3. **Social Choice:** 
   - *Next:* Arrow's Impossibility Theorem, Gibbard-Satterthwaite, and more general voting axioms.
4. **Markets (Matching & Platforms):** 
   - *Next:* Rural Hospitals Theorem, Top Trading Cycles (TTC).
5. **Econometrics:** 
   - *Next:* Causal inference primitives and structural estimation definitions.
6. **Learning (Bandits & Games):** 
   - *Next:* Multi-Armed Bandits (UCB proofs), No-Regret Dynamics, Correlated Equilibrium.
7. **Algorithms (Online & Complexity):** 
   - *Next:* Prophet Inequalities, PPAD definitions.

## Phase 3: AI Formalization Automation

As the core library grows robust, the final phase of the roadmap is transitioning this manual workflow into fully autonomous agent skills.

We will refine the `econcs-formalizer` skill so that future agents can:
- Ingest a new arXiv PDF.
- Automatically construct the `DependencyDAG.tex` and `MainTheorems.lean` template.
- Identify the necessary generic primitives to upstream into `EconCSLib`.
- Synthesize the required Lean 4 proofs to connect the paper's claims to the generic library.
