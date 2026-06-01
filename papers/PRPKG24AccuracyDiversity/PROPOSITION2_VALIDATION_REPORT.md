# Validation Report: PRPKG Proposition 2

## 1. Source and Scope

- Paper: *Reconciling the accuracy-diversity trade-off in recommendations*
- Source version: arXiv:2307.15142v1, cached locally as `PRPKG24AccuracyDiversity.pdf`
- Lean folder: `papers/PRPKG24AccuracyDiversity`
- Human-facing theorem file: `MainTheorems.lean`
- Main proof file: `Uniform.lean`
- Scope of this report: Proposition 2 only. This is not a final validation report for the whole paper.

## 2. Proposition Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Uniform `[0,1]` top-`k` objective | `uniformTopKValue`, `uniformTopKOrderStatisticSum_eq_value` | fully formalized | exact finite uniform instance | Proves the closed-form top-`k` order-statistic sum used by Proposition 2. |
| Paper-style `k` eligibility condition | `uniformTopK_eligible_of_paper_min_share_bound` | fully formalized | exact bridge | Converts the paper-style minimum square-root-share bound into the Lean tail-region condition. |
| Finite Proposition 2 analogue | `paper_proposition_2_uniform_top_k_finite_analogue_of_paper_bound` | partially formalized | minor deviation | Proves square-root-profile approximation for all eligible `k`, but with error `(2T+2)/N` instead of the paper's `(T+1)/N`. |
| Sharp finite-bound bridge | `paper_proposition_2_uniform_top_k_sharp_finite_of_count_closeness` | conditional | exact finite conclusion from named seam | Shows the paper's `(T+1)/N` conclusion follows from coordinate-closeness to the square-root homogeneity target. |
| Paper-route sharp finite-bound bridge | `paper_proposition_2_uniform_top_k_sharp_finite_of_printed_optimizer_closeness` | conditional | exact implication used by proof sketch | Shows that closeness within `T` of the displayed relaxed optimizer implies the paper's `(T+1)/N` conclusion, while the displayed optimizer's total mismatch remains recorded separately. |
| Asymptotic Proposition 2 consequence | `paper_proposition_2_uniform_top_k_asymptotic_of_paper_bound` | fully formalized relative to finite analogue | minor deviation | Uses exact-rate convergence from the finite `(2T+2)/N` bound. |
| Definition 2 sequence wrapper | `paper_proposition_2_uniform_top_k_sequence_homogeneity_of_paper_bound` | fully formalized relative to finite analogue | minor deviation | Gives sequence-level `1/2`-homogeneity for optimal allocation sequences under the Lean finite bound. |
| Printed relaxed optimizer audit | `paper_proposition_2_printed_relaxed_optimizer_total_mismatch` | fully formalized | caveat evidence | Shows the PDF's displayed relaxed optimizer coordinates sum to `N-T`, not `N`. |
| Corrected relaxed optimizer audit | `paper_proposition_2_corrected_relaxed_optimizer_total` | fully formalized | corrected formula | Shows the shifted optimizer used in Lean sums to `N`. |

## 3. Additional Assumptions Beyond Paper

- The finite Lean wrappers make positivity explicit: `0 < N`, `0 < k`, and `∀ t, 0 < likelihood t`.
- The all-eligible-`k` wrapper assumes the paper-style bound as a real inequality:
  `(k : ℝ) + 1 ≤ (N : ℝ) * uniformSqrtMinShare likelihood - T`.

## 4. Proof-Strategy Deviations

- Lean uses a finite no-crossing rounding route around lower and upper integer anchors, rather than the paper's general Lemma D.5 strictly-convex real-optimizer lemma.
- Lean uses the corrected shifted relaxed optimizer whose coordinates sum to `N`; the printed formula in the PDF sums to `N-T`.
- The sharp finite-bound bridge keeps the paper's Lemma D.5 route explicit:
  once `|a_t - x_t^*| <= T+1` is proved for the corrected square-root optimizer,
  the exact paper finite homogeneity bound follows without changing the
  currently verified asymptotic route.
- A second paper-route bridge starts from the displayed relaxed optimizer used
  in the PDF proof. That implication is formalized, but the optimizer's total
  mismatch means this is still not a full proof of the sharp finite theorem.

## 5. Conditional Results and Remaining Gaps

- The paper's exact finite error `(T+1)/N` is not formalized.
- The current unconditional finite theorem proves `(2T+2)/N`, which is enough for the asymptotic and sequence-limit conclusions but not the sharp finite constant.
- The sharp finite bridge reduces the remaining paper finite-constant gap to
  the specific coordinate-closeness proof supplied informally by Lemma D.5.
- The general order-statistic identity of Proposition 5 remains abstract outside the uniform instance used here.

## 6. Suspected Paper Errors or Inconsistencies

- Proposition 2 proof, equation (200): the displayed relaxed optimizer appears to omit the type-count shift. Lean proves that `uniformSqrtPrintedOptTarget` sums to `N-T`; the corrected `uniformSqrtRealOptTarget` sums to `N`.

## 7. Verdict

- Completion status for Proposition 2: partially formalized with a documented source caveat.
- The asymptotic `1/2`-homogeneity consequence is verified through a slightly weaker finite constant. The sharp paper finite bound remains open and should not be claimed as verified.
