# Who is in Your Top Three? Optimizing Learning in Elections with Many Candidates

## Source Version

- Paper: *Who is in Your Top Three? Optimizing Learning in Elections with Many Candidates*
- Authors: Nikhil Garg, Lodewijk Gelauff, Sukolsak Sakshuwong, Ashish Goel
- Publication venue: HCOMP 2019
- Version formalized: arXiv version, 2019
- Official URL: https://arxiv.org/abs/1906.08160
- Public PDF: https://arxiv.org/pdf/1906.08160.pdf
- Source cache used for intake: arXiv TeX source from `https://arxiv.org/e-print/1906.08160`

The source PDF and extracted source cache are local/ignored artifacts. Do not
commit them unless redistribution rights are checked separately.

## Current Status

Status: formalized.

This folder contains the finite large-deviation and aggregation layer for the
paper, K-approval/Mallows endpoints, and the randomization comparison surface.
The Lean files compile and expose source-labeled endpoints for Proposition
1-4, randomized scoring, pairwise K-approval no-randomization, the constructed
W-selection randomization-improvement example, Mallows no-randomization, and
the high-noise Mallows W-approval non-optimality example.

The main shared-library dependency is
`EconCSLib.Foundations.Probability.FiniteSupportMGF`,
`EconCSLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts`,
`EconCSLib.Foundations.Probability.FiniteTypeLogMass`, and
`EconCSLib.Foundations.Probability.LargeDeviations`. The empirical/numerical
sections are treated as reproducibility artifacts rather than Lean theorem
targets.

## Paper-Facing Ledger

- Implementation theorem file: `GGSG19TopThree/MainTheorems.lean`
- Human-facing theorem file: `GGSG19TopThree/PaperInterface.lean`
- Detailed proof interface: `GGSG19TopThree/ProofInterface.lean`
- Source-labeled compatibility import: `GGSG19TopThree/SourceTheorems.lean`
- Machine-readable status source: `GGSG19TopThree/status.json`
- Outside-Lean proof plan: `GGSG19TopThree/FORMALIZATION_PLAN.md`
- Final validation report: `GGSG19TopThree/FINAL_VALIDATION_REPORT.md`
- Detailed post-formalization audit: `GGSG19TopThree/POST_FORMALIZATION_AUDIT.md`
- Dependency DAG: `GGSG19TopThree/DependencyDAG.tex`

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Definition: large-deviation rate | `paper_definition_large_deviation_rate` | formalized | `PaperInterface.lean` | None |
| Proposition 1 design invariance | `source_proposition1_thm_consistency_tiered` | formalized | `PaperInterface.lean` | None |
| Proposition 2 pairwise scoring-rate formula | `source_proposition2_thm_pairwiselearning_finite_support` | formalized | `PaperInterface.lean` | None |
| Proposition 3 K-approval pairwise-rate formula | `source_proposition3_lem_pairwiselearning_approval_finite_ternary` | formalized | `PaperInterface.lean` | None |
| Proposition 4 outcome learning finite aggregation | `source_proposition4_thm_goal_learning_finite_support` | formalized | `PaperInterface.lean` | None |
| Theorem 1 randomized scoring | `source_theorem1_lem_randomizebetterscoring` | formalized | `PaperInterface.lean` | None |
| Theorem 2 randomized K-approval | `source_theorem2_lem_randomizenotbetterapproval_pairwise` | formalized | `PaperInterface.lean` | None |
| Randomization helps for W-selection | `source_theorem_lem_randomizebetterapproval_w_selection_constructed` | formalized | `PaperInterface.lean` | None |
| Mallows no-randomization | `source_corollary_lem_mallowsnorando` | formalized | `PaperInterface.lean` | None |
| Mallows W-approval non-optimality | `source_theorem_lem_mallowsnotWK_counterexample` | formalized | `PaperInterface.lean` | None |

## Validation

Last targeted check:

```bash
lake build GGSG19TopThree
```
