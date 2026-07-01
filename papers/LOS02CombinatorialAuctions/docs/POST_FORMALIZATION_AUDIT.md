# LOS02 Post-Formalization Audit

This file preserves the detailed implementation/status ledger that was
previously mixed into `FINAL_VALIDATION_REPORT.md`. The final validation report
is now kept short and human-facing; use this audit file for source inventory,
formalized Lean surface detail, validation commands, public-release closeout
notes, and future pickup context.

Date: 2026-05-24; public-release closeout refreshed 2026-05-31

## Source Inventory

- Paper: Daniel Lehmann, Liadan Ita O'Callaghan, and Yoav Shoham,
  *Truth Revelation in Approximately Efficient Combinatorial Auctions*,
  Journal of the ACM 49(5), 2002.
- Local source files:
  - `LOS02CombinatorialAuctions.pdf` is cached locally and ignored.
  - The extracted text cache used for source-numbered statement searches is
    local-only and omitted from the public repository.

The source-audit pass found the named surface tracked in the folder README:
Definitions 3.1--3.2, Theorem 4.1, Proposition 4.2, Definition 5.1, Theorem
6.1, Definition 7.1, Theorem 7.2, Lemmas 9.1--9.5, Theorem 9.6, Definition
10.1, Theorem 10.2, and the short complexity-class note after Theorem 6.1.

For future pickup, read `START_HERE_NEXT_AGENT.md`, which points to the full
handoff note and proof path forward.

## Formalized Lean Surface

- Direct combinatorial-auction utility and truthfulness predicates are exposed
  through `PaperInterface.utility` and `PaperInterface.truthfulOn`.
- The generalized Vickrey auction route is closed:
  `theorem4_1_generalized_vickrey_truthful` and
  `proposition4_2_generalized_vickrey_truthful_utility_nonneg`.
- Theorem 6.1's reduction layer is closed up to the repository's explicit
  complexity boundary:
  clique-to-complement-independent-set, clique-to-set-packing,
  graph-incidence independent-set-to-set-packing, set-packing-to-single-minded
  feasibility/value encoding, allocation, threshold-decision reductions from
  clique through complement independent set, set packing, and single-minded
  welfare, exact solver transfer, approximation-preserving transfer, and
  conditional external-complexity consequence wrappers, including
  reduction-closed hardness-transfer wrappers and named abstract `NP = ZPP`
  wrappers over `EconCSLib.Complexity.ComplexityClassModel`.
- The source complexity-class note after Theorem 6.1 is represented
  abstractly: `P = NP` implies `NP = ZPP`, and `NP = ZPP` implies the packaged
  `NP = RP`, `NP = co-RP`, and `NP = co-NP` collapse for any supplied
  `RandomizedComplexityClassModel`.
- Theorem 7.2 is closed for sorted greedy orders, including rejected-bid
  blocker extraction, blocking-certificate counting, common-bid removal,
  reduced-disjoint reasoning, and add-back.
- Lemmas 9.1--9.5 and Theorem 9.6 are closed for the source nonempty,
  nonnegative single-minded domain using finite-or-infinite critical-value
  certificates.
- Definition 10.1's average-order greedy payment rule is represented directly,
  including denied/no-next/next payment cases and accepted-bid criticality.
- Theorem 10.2 is closed for the concrete average-order greedy accepted-set and
  payment mechanism on the source nonempty, nonnegative single-minded domain,
  including the average-order strengthened-bid movement lemma used for
  monotonicity.

## Remaining Boundary

The folder remains marked `Partially formalized`, not `Formalized`, only because
the reusable library does not yet model native machine-level computational
complexity classes, polynomial-time algorithms, randomized algorithms, or the
Karp/Hastad hardness proofs. The paper-facing Theorem 6.1 complexity
consequences are therefore exposed as conditional external-consequence wrappers
over external Karp/Hastad-style hardness facts, with the `NP = ZPP` conclusion
represented by an abstract class model and the source randomized-class note
represented by abstract class-relationship fields.

No paper-facing auction, greedy approximation, critical-price, or
single-minded-truthfulness endpoint is left open in the current model.

## Public-Release Closeout

LOS02 is suitable as a public partial formalization under the same policy as
LMMS04: the exposed gap is reusable library infrastructure, not hidden
paper-specific proof debt. The remaining work is to replace the abstract
external-consequence hypotheses with a native computational-complexity layer
covering polynomial-time many-one reductions, NP-hardness/inapproximability
facts for the cited set-packing/clique route, randomized classes such as ZPP,
and the machine-level meaning of polynomial-time algorithms.

Until that reusable layer exists, the public status should remain
`Partially formalized`: all LOS02 auction, greedy approximation,
critical-price, and single-minded-truthfulness endpoints are formalized, while
Theorem 6.1's final machine-level complexity consequences remain conditional on
external Karp/Hastad-style complexity facts.

## Validation Commands

- `lake build LOS02CombinatorialAuctions`
- `lake build EconCSLib.Algorithms.Complexity.Classes`
- `lake build EconCSLib`
- `latexmk -pdf DependencyDAG.tex`
- `latexmk -c DependencyDAG.tex`
- `git diff --check -- EconCSLib/Algorithms/Complexity/Classes.lean EconCSLib/Basic.lean EconCSLib/MechanismDesign/Auctions/Combinatorial.lean docs/ECONCSLIB_DOMAIN_INDEX.md README.md docs/ECONCSLEAN_CURRENT_STATUS.md papers/LOS02CombinatorialAuctions/MainTheorems.lean papers/LOS02CombinatorialAuctions/PaperInterface.lean papers/LOS02CombinatorialAuctions/README.md papers/LOS02CombinatorialAuctions/FORMALIZATION_PLAN.md papers/LOS02CombinatorialAuctions/FINAL_VALIDATION_REPORT.md papers/LOS02CombinatorialAuctions/DependencyDAG.tex papers/LOS02CombinatorialAuctions/status.json papers/LOS02CombinatorialAuctions/HANDOFF_2026-05-24.md papers/LOS02CombinatorialAuctions/START_HERE_NEXT_AGENT.md skills/econcs-formalizer/SKILL.md skills/econcs-formalizer/references/proof-algorithms-complexity.md`
- `python3 scripts/audit_repository.py`

`lake build LOS02CombinatorialAuctions`,
`lake build EconCSLib.Algorithms.Complexity.Classes`, `lake build EconCSLib`,
the DAG PDF build/clean, and the scoped `git diff --check` all passed at the
time of this audit. The current public interface split exposes 30 LOS02
dashboard rows through `PaperInterface.lean`; proof-facing compatibility rows
live in `ProofInterface.lean`.
