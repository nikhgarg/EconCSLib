# Final Validation Report: GGSG19 Top Three

## 1. Human Verdict

- Lean formalization status: formalized
- Human dashboard review status: 0/10 rows reviewed; 0 stale; 0 mismatches.
- Axiom/premise/source-hygiene audit: 9/9 explicit premises are source-matched or derived from source primitives.

- Lean formalization status: formalized.
- Human dashboard review status: 0 reviewed rows, 0 stale rows, 0 mismatch rows, 10 total rows.
- Paper correctness verdict: no source error found for the formalized finite-candidate theorem surface.
- Qualitative proof verdict: the finite-candidate theorem surface is exposed
  with explicit finite-support boundary handling. The remaining visible
  premises are source-matched or derived from source primitives.
- Lean footprint: 34,984 paper-local Lean LOC, 308 `PaperInterface.lean` LOC, 10 review rows.

<!-- transitive-source-premise-audit:start -->
### Axiom, Premise, And Source-Hygiene Audit

The current axiom/premise/source-hygiene audit passes for full-status provenance. It uses Lean-native #print axioms for transitive proof debt, expanded paper-facing signatures for visible premises, and source-assumption ledgers for any non-derived assumptions.

Current result: no unresolved hidden source-row or certificate premise remains in the paper-facing review surface.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

- Paper: *Who is in Your Top Three? Optimizing Learning in Elections with Many Candidates*.
- Publication venue: HCOMP 2019.
- Source version: arXiv 1906.08160 TeX/PDF, 2019.
- Lean folder: `papers/GGSG19TopThree`.
- Human-facing theorem file: `papers/GGSG19TopThree/PaperInterface.lean`.
- Detailed post-formalization audit: `papers/GGSG19TopThree/POST_FORMALIZATION_AUDIT.md`.
- DAG artifacts: `papers/GGSG19TopThree/DependencyDAG.tex`, `papers/GGSG19TopThree/DependencyDAG.pdf`.

## 3. What Has Been Proven

The formalization covers the finite-candidate source theorem surface: the
large-deviation-rate definition, Propositions 1-4, randomized scoring,
randomized K-approval, the constructed W-selection randomization-improvement
example, Mallows no-randomization, and the high-noise Mallows W-approval
non-optimality example.

Propositions 2-4 expose the finite-support one-sided and eventually-zero
boundary cases explicitly. These are source-model boundary cases, not remaining
proof obligations.

Proposition 4's paper interface now uses the paper's source-shaped unweighted
expected-error sum `Q^N`. The older generalized positive-weight aggregate is
kept only as proof/library infrastructure, not as the paper-facing row.

The paper's empirical and numerical sections are treated as reproducibility
artifacts rather than Lean theorem targets.

## 4. Paper Definitions Checked

- Large-deviation rate: `r = -lim_N (1 / N) log A_N`.
  Lean: `paper_definition_large_deviation_rate`.

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| abbrev paper_definition_large_deviation_rate | `paper_definition_large_deviation_rate` | - Paper definition of an exponential large-deviation rate. |
<!-- lean-derived-definitions:end -->

## 5. Named Theorem Statements Checked

### Proposition 1

**Paper statement.** Strict top-prefix cross-tier dominance characterizes the
source tiered consistency/design-invariance condition.

**Lean interface statement.**
- `source_proposition1_thm_consistency_tiered`: tiered finite-ranking form.

**Status.** formalized.

### Propositions 2-4

**Paper statement.** Pairwise score-gap rates, K-approval ternary rates, and
finite relevant-pair aggregation give the outcome-learning rate.

**Lean interface statements.**
- `source_proposition2_thm_pairwiselearning_finite_support`.
- `source_proposition3_lem_pairwiselearning_approval_finite_ternary`.
- `source_proposition4_thm_goal_learning_finite_support`.

**Status.** formalized.

### Randomization and Mallows Results

**Paper statement.** Static scoring/K-approval comparisons and the Mallows
examples establish the paper's no-randomization and randomization-improvement
claims.

**Lean interface statements.**
- `source_theorem1_lem_randomizebetterscoring`.
- `source_theorem2_lem_randomizenotbetterapproval_pairwise`.
- `source_theorem_lem_randomizebetterapproval_w_selection_constructed`.
- `source_corollary_lem_mallowsnorando`.
- `source_theorem_lem_mallowsnotWK_counterexample`.

**Status.** formalized.

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem source_proposition1_thm_consistency_tiered | `source_proposition1_thm_consistency_tiered` | tiered finite-ranking form. |
| theorem source_proposition2_thm_pairwiselearning_finite_support | `source_proposition2_thm_pairwiselearning_finite_support` | - Source Proposition `thm:pairwiselearning`, finite-support form. The ordinary two-sided case has the paper's displayed Chernoff exponent; the explicit one-sided branches record finite-candidate boundary cases where the finite real rate... |
| theorem source_proposition3_lem_pairwiselearning_approval_finite_ternary | `source_proposition3_lem_pairwiselearning_approval_finite_ternary` | - Source Proposition `lem:pairwiselearning_approval`, finite ternary form for K-approval score gaps. The finite-rate branch is exactly the paper's closed form `approvalPairwiseRate`; the other branch is the strict boundary where the mist... |
| theorem source_proposition4_thm_goal_learning_finite_support | `source_proposition4_thm_goal_learning_finite_support` | - Source Proposition `thm:goal_learning`, finite relevant-pair aggregation form. The finite aggregate has an exact finite exponent unless all relevant pairwise errors are eventually empty, represented as extended rate `⊤`. |
| theorem source_theorem1_lem_randomizebetterscoring | `source_theorem1_lem_randomizebetterscoring` | - Source Theorem `lem:randomizebetterscoring`, finite W-selection form. The convex-combination static rule is reasonable, selects the target W-set, and weakly dominates the randomized scoring rule in extended finite outcome rate. |
| theorem source_theorem2_lem_randomizenotbetterapproval_pairwise | `source_theorem2_lem_randomizenotbetterapproval_pairwise` | - Source Theorem `lem:randomizenotbetterapproval`, fixed-pair form. For any finite randomized K-approval rule, some static component weakly dominates the randomized pairwise rate; zero-base static boundaries are treated as top extended r... |
| theorem source_theorem_lem_randomizebetterapproval_w_selection_constructed | `source_theorem_lem_randomizebetterapproval_w_selection_constructed` | - Source Theorem `lem:randomizebetterapproval_Wselection`, concrete finite constructed-law endpoint: the six-ranking law is design-invariant for W-selection and 50/50 randomized approval strictly beats every static K-approval cutoff in t... |
| theorem source_corollary_lem_mallowsnorando | `source_corollary_lem_mallowsnorando` | - Source Corollary `lem:mallowsnorando`: under a finite Mallows model with `q < 1`, an approval-rate-optimal static K-approval cutoff weakly dominates any finite randomized family of nontrivial K-approval rules. |
| theorem source_theorem_lem_mallowsnotWK_counterexample | `source_theorem_lem_mallowsnotWK_counterexample` | - Source Theorem `lem:mallowsnotWK`: a four-candidate high-noise Mallows counterexample where W-approval is not approval-rate optimal. |
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GGSG19TopThree --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| abbrev paper_definition_large_deviation_rate | `paper_definition_large_deviation_rate` | None recorded | None |
| theorem source_corollary_lem_mallowsnorando | `source_corollary_lem_mallowsnorando` | None recorded | None |
| theorem source_proposition1_thm_consistency_tiered | `source_proposition1_thm_consistency_tiered` | None recorded | None |
| theorem source_proposition2_thm_pairwiselearning_finite_support | `source_proposition2_thm_pairwiselearning_finite_support` | None recorded | None |
| theorem source_proposition3_lem_pairwiselearning_approval_finite_ternary | `source_proposition3_lem_pairwiselearning_approval_finite_ternary` | None recorded | None |
| theorem source_proposition4_thm_goal_learning_finite_support | `source_proposition4_thm_goal_learning_finite_support` | None recorded | None |
| theorem source_theorem1_lem_randomizebetterscoring | `source_theorem1_lem_randomizebetterscoring` | None recorded | None |
| theorem source_theorem2_lem_randomizenotbetterapproval_pairwise | `source_theorem2_lem_randomizenotbetterapproval_pairwise` | None recorded | None |
| theorem source_theorem_lem_mallowsnotWK_counterexample | `source_theorem_lem_mallowsnotWK_counterexample` | None recorded | None |
| theorem source_theorem_lem_randomizebetterapproval_w_selection_constructed | `source_theorem_lem_randomizebetterapproval_w_selection_constructed` | None recorded | None |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Paper Assumption Provenance

> Axiom/premise/source-hygiene audit update (2026-06-12): `assumption_match_llm.json`
> records per-premise judgments for this paper's `Assumptions.lean` ledger.
> Current result: 9/9 explicit premises are source-matched or derived from
> source primitives, and 0/9 remain partial boundaries.

Every non-derived paper-facing premise is routed through
`GGSG19TopThree/Assumptions.lean` and checked by
`assumption_match_llm.json`. These rows are source theorem/domain conditions:
strict cross-tier prefix separation, ternary K-approval score gaps,
randomized-mechanism probability weights, and nontrivial
Mallows/K-approval domains. None are proof-only certificates.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_strict_cross_tier_no_ties` | source text | Proposition 1 strict cross-tier top-prefix inequalities. |
| `assumption_pairwise_approval_ternary_gap_domain` | derived from source primitives | Proposition 3 K-approval ternary score-gap domain and `s_i > s_j`. |
| `assumption_randomized_mechanism_probability_weights` | source model primitive | Randomized scoring/K-approval rule probabilities. |
| `assumption_mallows_nontrivial_winner_and_noise` | paper condition | Mallows top-W pivotal-pair regime, including the non-uniform Mallows domain. |
| `assumption_nontrivial_k_approval_cutoffs` | source text | Positive proper K-approval cutoffs in the randomized family. |

## 8. Proof-Strategy Deviations

- Propositions 2-4: Lean states finite-support boundary branches explicitly
  rather than folding them into prose.
- Empirical/numerical sections: treated as reproducibility artifacts outside
  the Lean theorem surface.

## 9. Proof Tricks Worth Reusing

- Use `WithTop` rates for finite-support large-deviation boundary cases.
- Split ranking-learning proofs into pairwise finite-support rates, K-approval
  ternary specialization, and finite relevant-pair aggregation.
- Keep one-loser/all-but-one K-approval facts in the shared social-choice
  library and paper-specific terminology as thin wrappers.

## 10. Library Lift Pass

- `EconCSLib.Foundations.Probability.FiniteSupportMGF`: finite-support
  log-MGF, rate, extended-rate, and pairwise threshold-rate APIs.
- `EconCSLib.Foundations.Probability.LargeDeviations`: finite weighted-sum and
  pairwise aggregation certificates.
- `EconCSLib.SocialChoice.Ranking.Approval`: all-but-one K-approval last-rank
  probability facts.
- `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization`: reusable Mallows
  rank-factorization algebra.

Further candidates are recorded in `POST_FORMALIZATION_AUDIT.md`.

## 11. DAG Audit

- Rendered artifact: yes, `DependencyDAG.pdf`.
- Topology: source-facing named-result topology; empirical sections omitted.
- Layout: visually inspected after rerendering; no known overlap or unintended
  dashed-edge semantics.

## 12. Conditional Results and Remaining Gaps

None for the source-facing finite-candidate theorem surface.

## 13. Suspected Paper Errors or Inconsistencies

None.

## 14. Validation Checks

The targeted paper build passed for `lake build GGSG19TopThree`. The DAG was
rendered from the paper folder with `latexmk`, converted to PNG, and visually
inspected. Targeted `git diff --check` passed for the changed GGSG documents.

## 15. Final Verdict

- Completion status: formalized.
- Summary: The finite-candidate source theorem surface is represented in Lean,
  including the finite-support boundary branches and randomized pivotal-pair
  cases exposed in the paper-facing interface.
