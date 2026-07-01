# Post-Formalization Audit: GGSG19 Top Three

## Scope

This audit is the detailed post-formalization ledger for *Who is in Your Top
Three? Optimizing Learning in Elections with Many Candidates*. The
human-facing status entrypoint is `FINAL_VALIDATION_REPORT.md`.

Publication venue: HCOMP 2019. The formalized source is the arXiv
1906.08160 TeX/PDF cache used during intake. The source PDF/text cache is a
local reference artifact and is not part of the public theorem surface.

Current status: formalized for the source-facing finite-candidate theorem
surface exposed in `PaperInterface.lean`. The detailed proof API lives in
`ProofInterface.lean`; the compact human-review surface has 10 source-shaped
rows.

## Named Source Inventory

| Source item | Current status | Notes |
|---|---|---|
| Large-deviation rate definition | formalized | Exposed as `paper_definition_large_deviation_rate`. |
| Proposition 1 | formalized | Strict cross-tier top-prefix dominance gives the source outcome notion; same-tier ties are compatible with the paper's tiered goal. |
| Proposition 2 | formalized | Finite-support score-gap Chernoff/rate endpoint with explicit one-sided and eventually-zero boundary branches. |
| Proposition 3 | formalized | K-approval ternary score-gap specialization and closed-form approval rate; represented as one source proposition rather than split helper boxes. |
| Proposition 4 | formalized | Relevant-pair finite aggregation gives the outcome-learning rate from pairwise rate certificates. |
| Theorem 1 | formalized | Convex-combination static scoring rule is consistent and weakly dominates randomized scoring. |
| Theorem 2 | formalized | Some static K-approval component weakly dominates each randomized pairwise K-approval rate. |
| Mallows Corollary | formalized | For Mallows `q < 1`, an optimal static K-approval rule weakly dominates randomized K-approval. |
| Randomization-helps theorem | formalized | Constructed W-selection law where randomized approval beats all static K cutoffs. |
| Mallows W-approval theorem | formalized | Four-candidate high-noise Mallows counterexample where W-approval is not approval-rate optimal. |
| Empirical/numerical sections | out of Lean scope | Treated as reproducibility artifacts, not theorem targets or DAG nodes. |

## Source-Deviation Notes

Proposition 1: the Lean endpoint follows the source strict cross-tier regime.
Exact cross-tier equality is outside that strict condition. Within-tier score
ties are allowed by the paper's outcome notion and are not a caveat.

Propositions 2-4: the Lean endpoints make finite-support boundary behavior
explicit through one-sided and eventually-zero branches. These are boundary
cases of the formal finite-candidate model, not remaining certificates or
conditional assumptions.

The paper's empirical/numerical sections are excluded from the theorem DAG and
the human-review theorem surface. Mention them in validation reports as scope
notes rather than as missing formalization rows.

## DAG Audit

`DependencyDAG.tex` uses the shared TikZ preamble and records HCOMP 2019 as the
publication venue while preserving the arXiv URL as the formalized source.

The DAG is source-facing:

- Every source-named proposition, theorem, and corollary in the formalized
  theorem surface appears as a node.
- Each numbered result appears as one source-result node. Proposition 1,
  Proposition 2, and Proposition 3 are not split into formula/helper/result
  boxes.
- Green result nodes state the paper-facing mathematical conclusion rather
  than source TeX labels or Lean declaration names.
- Empirical/numerical/reproducibility sections are not DAG nodes.
- The Mallows boundary pivotality layer is a supporting lemma node, not a
  caveat node feeding green paper results.
- Solid arrows represent Lean-checked formal dependencies. There should be no
  dashed or caveat edge feeding a green source theorem unless the dashed edge is
  explicitly documented as a non-required paper-route note.

Rendered artifact: `DependencyDAG.pdf`. After substantive DAG edits, rerender
from the paper folder and inspect the PDF or a PNG conversion for overlap,
stale venue/source metadata, missing theorem numbers, and unintended dashed
edges.

Current visual check: rerendered to PDF, converted to PNG, and inspected. The
current DAG has one box per numbered result, no source TeX labels or Lean
declaration names in node text, and no known box overlap, label overlap, or
arrow-through-text issue.

## Human Review Surface

`PaperInterface.lean` is the compact human-facing surface. It intentionally
contains 10 source-shaped rows:

- `paper_definition_large_deviation_rate`
- `source_proposition1_thm_consistency_tiered`
- `source_proposition2_thm_pairwiselearning_finite_support`
- `source_proposition3_lem_pairwiselearning_approval_finite_ternary`
- `source_proposition4_thm_goal_learning_finite_support`
- `source_theorem1_lem_randomizebetterscoring`
- `source_theorem2_lem_randomizenotbetterapproval_pairwise`
- `source_theorem_lem_randomizebetterapproval_w_selection_constructed`
- `source_corollary_lem_mallowsnorando`
- `source_theorem_lem_mallowsnotWK_counterexample`

Auxiliary finite-rate formulas, certificate structures, long Mallows
probability derivations, and implementation helper lemmas remain in
`ProofInterface.lean`, `MainTheorems.lean`, and the Mallows-specific modules.
They should not be added to `PaperInterface.lean` unless they become
source-facing review rows.

## Library Extraction Review

Already-elevated reusable infrastructure used by this proof includes:

- `EconCSLib.Foundations.Probability.FiniteSupportMGF` for finite-support
  MGFs/log-MGFs, finite Legendre values, real and `WithTop` rate functions,
  `withTopRealScale`, finite score-gap/rating LDP wrappers, and pairwise
  threshold-rate objectives.
- `EconCSLib.Foundations.Probability.LargeDeviations` for exact-rate,
  upper-bound, lower-bound, weighted-sum, and pairwise aggregation
  certificates.
- `EconCSLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts` and
  `FiniteTypeLogMass` for support-aware finite type/count lower-bound
  machinery.
- `EconCSLib.SocialChoice.Ranking.Approval` for `approvedByK`, pair-up/down
  probabilities, `lastRank`, and all-but-one K-approval last-rank probability
  facts used by GGSG one-loser wrappers.
- `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization` for reusable
  Mallows rank-factorization and first-weight algebra.

Further extraction candidates:

- GGSG's Mallows one-loser last-rank weight/probability formulas are good
  candidates for `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization` or
  a Mallows approval module if another paper needs last-rank Mallows mass
  comparisons.
- Top-W boundary-pair selection packages in the GGSG Mallows files should stay
  paper-local until a second paper needs the same W-selection boundary
  abstraction.

## Commands

Current validation target:

```bash
lake build GGSG19TopThree
```

DAG refresh target:

```bash
cd papers/GGSG19TopThree
latexmk -pdf -interaction=nonstopmode DependencyDAG.tex
```

When this audit, DAG, or review surface changes, also run targeted
`git diff --check` on the changed files.
