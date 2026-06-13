# Final Validation Report: Producer Fairness

## 1. Human Verdict

- Lean formalization status: formalized
- LLM statement-translation audit: 17/17 dashboard rows match; 0 stale, missing, uncertain, or mismatch rows.
- Human dashboard review status: 10/17 rows have saved human review entries; 0 stale entries; 0 human mismatches.
- Human review notes: 8 reviewed rows were marked matching. Two reviewed rows were marked uncertain because the human review depends on trusting shared-library predicates (`EconCSLib.Statistics.JensenConvex` and `EconCSLib.Statistics.GlobalMinAt`).
- Human summary: Formalization required an interior-quality assumption (`0 < q_v < 1`) for the strict variance-decrease statement.

<!-- transitive-source-premise-audit:start -->
### Transitive Source-Premise Audit

The strengthened recursive source-premise audit passes for full-status provenance. It follows paper-local wrappers and reusable-library certificate APIs, and treats certificate/source-row/external-boundary premises as full-status blockers unless they are derived internally or routed through validated paper assumptions.

Current result: The strengthened transitive provenance audit finds no unresolved certificate/source-boundary dependency for the current paper-facing status; the documented MBJG caveat remains the zero-denominator/utility-domain boundary already described in the report.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

- Paper: *Balancing Producer Fairness and Efficiency via Prior-Weighted Rating System Design*
- Source version: [arXiv:2207.04369](https://arxiv.org/abs/2207.04369) / ICWSM 2025
- Lean folder: `MBJG25ProducerFairness/`
- Human-facing theorem file: `MBJG25ProducerFairness/PaperInterface.lean`
- DAG artifacts: `MBJG25ProducerFairness/DependencyDAG.tex`

## 3. What Has Been Proven

The paper-facing definitions and named results compile in Lean; detailed definition, theorem, and validator ledgers are collected at the end of the report. The current LLM statement-translation audit validates all 17 dashboard rows against the context-free Lean-to-TeX drafts. The saved human dashboard review is partial: 10 rows have human entries, two of those entries are intentionally marked uncertain because they require deciding how much trust to place in shared-library predicates, and 7 rows still need initial human review.

## 4. Paper Assumption Provenance And Modeling Notes

> Strict premise-source audit update (2026-06-12): `assumption_match_llm.json` records per-premise judgments for this paper's `Assumptions.lean` ledger. Current result: 11/11 visible premises are judged as source model primitives, paper-statement conditions, or the documented strict-variance caveat; 0 premises remain as partial-formalization boundaries. The former nonzero-denominator proof condition for Theorem 3.2 convexity has been removed from the assumption ledger and is now derived in Lean from positive prior-shape mass, nonnegative prior strength, and positive time.

Every paper-facing theorem premise that is not derived in Lean is routed through
`Assumptions.lean` and checked separately as a paper/source condition or a
documented caveat.

| Assumption or condition | Lean declaration | Source location / statement | Validators | Comments |
|---|---|---|---|---|
| Positive prior-shape mass | `assumption_positive_prior_shape` | Section 2.1 prior-weighted rating model / Theorems 3.1 and 3.2 | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Required by the displayed posterior denominator. |
| Positive time | `assumption_positive_time` | Theorems 3.1 and 3.2, quality estimation after `t` timesteps | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Used by fixed-setting monotonicity rows. |
| Nonnegative time | `assumption_nonnegative_time` | Theorem 3.2 variance-as-quality-function rows | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Used by concavity and maximum-at-half rows. |
| Closed quality interval, lower bound | `assumption_quality_nonnegative` | Section 2.1 true quality `0 <= q_v <= 1` | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Source Bernoulli quality domain. |
| Closed quality interval, upper bound | `assumption_quality_at_most_one` | Section 2.1 true quality `0 <= q_v <= 1` | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Source Bernoulli quality domain. |
| Interior quality for strict variance decrease, lower bound | `assumption_quality_positive` | Theorem 3.1 strict variance-decrease repair | gpt-5-codex (model; documented_caveat; 2026-06-12T00:00:00Z) | Not in the literal theorem statement; needed because strict decrease fails at `q_v = 0`. |
| Interior quality for strict variance decrease, upper bound | `assumption_quality_lt_one` | Theorem 3.1 strict variance-decrease repair | gpt-5-codex (model; documented_caveat; 2026-06-12T00:00:00Z) | Not in the literal theorem statement; needed because strict decrease fails at `q_v = 1`. |
| Nonnegative prior strength | `assumption_prior_strength_nonnegative` | Section 2.1 prior strength `eta >= 0` | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Source prior-strength domain. |
| Ordered prior strengths, weak order | `assumption_prior_strength_weak_order` | Theorem 3.1 monotonicity in `eta` | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Weak comparison form. |
| Ordered prior strengths, strict order | `assumption_prior_strength_strict_order` | Theorem 3.1 monotonicity in `eta` | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Strict comparison form. |

### Additional Assumptions Beyond Paper

- The only non-source condition is the documented caveat `0 < q_v < 1` for
  strict variance decrease. It is recorded as a repair to the paper's boundary
  bug, not as a hidden proof assumption.
- The Theorem 3.2 convexity denominator condition is not exposed as a paper
  assumption. It is derived in Lean from source-domain conditions.

## 5. Proof-Strategy Deviations

- None. The proof follows the algebraic structure of the paper's fixed-model definitions.

## 6. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 7. Library Lift Pass

None separately recorded in the existing report.

## 8. DAG Audit

No separate DAG audit note is recorded in the existing report.

## 9. Conditional Results and Remaining Gaps

- All claimed fixed-model results are proved in Lean.
- Human dashboard review is not fully closed: 7 rows still need initial human review.
- The human review log flags a library-predicate trust boundary for `JensenConvex` and `GlobalMinAt`. The Lean definitions and proofs compile, and the LLM statement-translation audit matches them to the paper-facing claims, but final human review should decide how to audit the shared predicate meanings.

## 10. Suspected Paper Errors or Inconsistencies

- **Theorem 3.1 Strict Variance Decrease:** The paper states strict decrease in prior strength without excluding boundary qualities. However, at `q_v = 0` and `q_v = 1`, the Bernoulli variance is `0` regardless of prior strength. Lean formalization identified this bug and provided counterexamples (`paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero`).

## 11. Validation Checks

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

LLM summary: 17 rows; 17 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

Human-review summary: 10/17 rows have saved human entries; 8 reviewed rows are marked matching; 2 reviewed rows are marked uncertain; 0 saved entries are stale; 7 rows remain unreviewed; 0 rows are marked mismatch.

Human-review flags:
- Human reviewer marked `paper_facing_theorem3_2_squared_bias_convex_in_quality` uncertain because this requires trusting or auditing `EconCSLib.Statistics.JensenConvex`.
- Human reviewer marked `paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean` uncertain because this requires trusting or auditing `EconCSLib.Statistics.GlobalMinAt`.
- All saved human-review entries are current with respect to the dashboard statement hashes.

## 12. Final Verdict

- Completion status: formalized.
- Summary: The core mathematical results of the Prior-Weighted Rating System Design paper (Theorems 3.1 and 3.2) are formalized in Lean. A boundary bug in the strictness of the variance-decrease clause was identified and corrected with an interior-quality assumption. The LLM statement-translation audit is current and all-match. The human dashboard review is partially complete and records a remaining review policy question about shared-library predicates (`JensenConvex` and `GlobalMinAt`).

## 13. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| Posterior mean | `paper_posterior_mean` | Posterior mean estimated quality in the fixed binary rating model: `(eta * alpha + t * q_v) / (eta * (alpha + beta) + t)`. |
| Bias | `paper_bias` | Bias of the estimated quality: posterior mean minus true quality. |
| Variance | `paper_variance` | Variance of the estimated quality: `t * q_v * (1 - q_v) / (eta * (alpha + beta) + t)^2`. |
| Squared bias | `paper_squared_bias` | Squared bias of the estimated quality. |
| Individual producer unfairness | `paper_facing_individual_producer_unfairness` | Section 4 individual producer unfairness: standard deviation in selection rate among producers with the same true quality `q`. |
| Thompson sampling mechanism | `paper_facing_thompson_sampling_mechanism` | Section 4 Thompson sampling: draw from a belief distribution and pick an argmax. |
| Expected regret | `paper_facing_expected_regret` | Section 4 expected regret: total expected regret across a finite time horizon. |
<!-- lean-derived-definitions:end -->

## 14. Named Theorem Statements Checked

### Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Theorem 3.1, Var. Weak Decrease | `paper_facing_theorem3_1_variance_weak_decrease` | fully formalized | exact | Holds on closed interval `[0, 1]`. |
| Theorem 3.1, Var. Strict Decrease | `paper_facing_theorem3_1_variance_strict_decrease_interior` | fully formalized | minor deviation | Interior assumption `0 < q_v < 1` added to fix boundary bug. |
| Theorem 3.1, Bias Nondecreasing | `paper_facing_theorem3_1_squared_bias_nondecreasing` | fully formalized | exact | |
| Theorem 3.2, Bias Convexity | `paper_facing_theorem3_2_squared_bias_convex_in_quality` | fully formalized | model exact; human uncertainty | Human review asks how to audit or trust the shared `JensenConvex` predicate; denominator nonzero is derived from source-domain conditions. |
| Theorem 3.2, Bias Minimizer | `paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean` | fully formalized | model exact; human uncertainty | Human review asks how to audit or trust the shared `GlobalMinAt` predicate. |
| Theorem 3.2, Var. Concavity | `paper_facing_theorem3_2_variance_concave_in_quality` | fully formalized | exact | |
| Theorem 3.2, Var. Maximizer | `paper_facing_theorem3_2_variance_global_max_at_half` | fully formalized | exact | |
| Appx C, MSE Decomposition | `paper_facing_responsive_mse_decomposition` | fully formalized | exact | Treats the number of reviews $N$ as a random variable explicitly. |
| Section 4, Indiv. Unfairness | `paper_facing_individual_producer_unfairness` | fully formalized | exact | Maps standard deviation formula to variance metric explicitly. |
| Section 4, Thompson Sampling | `paper_facing_thompson_sampling_mechanism` | fully formalized | exact | Standard generalized definition. |
| Section 4, Expected Regret | `paper_facing_expected_regret` | fully formalized | exact | |

The context-free Lean-to-TeX drafts and source-facing statement judgments are
tracked in `lean_to_tex_llm.json` and `statement_match_llm.json`; the compact
human-facing ledger appears below.

## 15. Paper-Facing Statement Validator Ledger

Generated from the current dashboard status, condensed for PDF readability.
Detailed timestamped evidence remains in `.review_traces/paper_theorem_validations.jsonl`
and `statement_match_llm.json`.

| Review row | Human review | Model review | Comment |
| --- | --- | --- | --- |
| Posterior mean | match | match | Direct formula; identifies Lean `alpha`, `beta` with the paper's tilded shape parameters. |
| Bias | match | match | Posterior mean minus true quality. |
| Variance | match | match | Matches the paper variance formula. |
| Squared bias | match | match | Square of the bias definition. |
| Theorem 3.1 variance, weak | match | match | Corrected full-interval weak monotonicity statement. |
| Theorem 3.1 variance, strict | match | match | Adds the interior-quality condition `0 < q_v < 1`. |
| Theorem 3.1 squared bias | match | match | Same monotonic direction as the paper. |
| Theorem 3.2 squared-bias convexity | uncertain | match | Human review asks how to audit or trust shared predicate `JensenConvex`. |
| Theorem 3.2 squared-bias minimizer | uncertain | match | Human review asks how to audit or trust shared predicate `GlobalMinAt`. |
| Theorem 3.2 variance concavity | not yet reviewed | match | Model check matches the paper-facing concavity statement. |
| Theorem 3.2 variance maximizer | not yet reviewed | match | Model check matches the maximum-at-half statement. |
| Boundary caveat at `q_v = 0` | not yet reviewed | match | Records why unconditional strict decrease fails. |
| Boundary caveat at `q_v = 1` | not yet reviewed | match | Records why unconditional strict decrease fails. |
| Individual producer unfairness | match | match | Standard deviation of selection rates among equal-quality producers. |
| Thompson sampling mechanism | not yet reviewed | match | Draw a quality profile from the belief and choose an argmax. |
| Expected regret | not yet reviewed | match | Finite-horizon expected regret. |
| Appendix C MSE decomposition | not yet reviewed | match | Handles random review count `N` explicitly. |

All saved human-review entries are current. The remaining open human-review work
is the set of rows marked `not yet reviewed`, plus the policy question around
how to audit shared-library predicates used by rows marked `uncertain`.
