# Validation Report: PRPKG Proposition 2

## 1. Source and Scope

- Paper: *Reconciling the accuracy-diversity trade-off in recommendations*
- Source version: arXiv:2307.15142v1; this checkout has the extracted source
  text cache `PRPKG24AccuracyDiversity.txt`, while the ignored PDF cache is not
  present locally
- Lean folder: `papers/PRPKG24AccuracyDiversity`
- Human-facing theorem file: `MainTheorems.lean`
- Main proof file: `Uniform.lean`
- Scope of this report: Proposition 2 and its downstream homogeneity use.

## 2. Proposition Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Uniform `[0,1]` top-`k` objective | `uniformTopKValue`, `uniformTopKOrderStatisticSum_eq_value` | formalized | exact finite uniform instance | Proves the closed-form top-`k` order-statistic sum used by Proposition 2. |
| Paper-style `k` eligibility condition | `uniformTopK_eligible_of_paper_min_share_bound` | formalized | exact bridge | Converts the paper-style minimum square-root-share bound into the Lean tail-region condition. |
| Corrected finite Proposition 2 bound | `paper_proposition_2_uniform_top_k_corrected_finite_of_paper_bound` | formalized | corrected finite constant | Proves square-root-profile approximation for all eligible `k` with error `(2T+1)/N`. This is a factor-2 corrected finite bound relative to the printed sharp constant. |
| Asymptotic Proposition 2 consequence | `paper_proposition_2_uniform_top_k_corrected_asymptotic_of_paper_bound` | formalized | paper homogeneity conclusion | Uses exact-rate convergence from the finite `(2T+1)/N` bound. The downstream paper use needs a vanishing `O(1/N)` error, not the printed sharp finite constant. |
| Definition 2 sequence wrapper | `paper_proposition_2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound` | formalized | paper sequence conclusion | Gives sequence-level `1/2`-homogeneity for optimal allocation sequences under the corrected finite bound. |
| Printed relaxed optimizer audit | `paper_proposition_2_printed_relaxed_optimizer_total_mismatch` | formalized | source-deviation evidence | Shows the PDF's displayed relaxed optimizer coordinates sum to `N-T`, not `N`. |
| Corrected relaxed optimizer audit | `paper_proposition_2_corrected_relaxed_optimizer_total` | formalized | corrected formula | Shows the shifted optimizer used in Lean sums to `N`. |
| Sharp finite-bound bridge | `paper_proposition_2_uniform_top_k_sharp_finite_of_count_closeness` | auxiliary conditional | exact finite conclusion from named seam | Shows the paper's `(T+1)/N` conclusion follows from coordinate-closeness to the square-root homogeneity target. This is retained only as a source-repair seam. |
| Paper-route sharp finite-bound bridge | `paper_proposition_2_uniform_top_k_sharp_finite_of_printed_optimizer_closeness` | auxiliary conditional | exact implication used by proof sketch | Shows that closeness within `T` of the displayed relaxed optimizer implies the paper's `(T+1)/N` conclusion, while the displayed optimizer's total mismatch remains recorded separately. |

## 3. Assumptions Made Explicit

- The finite Lean wrappers make positivity explicit: `0 < N`, `0 < k`, and
  `∀ t, 0 < likelihood t`.
- The all-eligible-`k` wrapper assumes the paper-style bound as a real
  inequality:
  `(k : ℝ) + 1 ≤ (N : ℝ) * uniformSqrtMinShare likelihood - T`.

These are the natural nondegeneracy and eligibility hypotheses used by the
paper argument.

## 4. Proof-Strategy Deviations

- Lean uses a finite no-crossing rounding route around lower and upper integer
  anchors, rather than relying on the paper's informal Lemma D.5 step as a
  black box.
- Lean uses the corrected shifted relaxed optimizer whose coordinates sum to
  `N`; the printed formula in the PDF sums to `N-T`.
- Replacing the displayed optimizer by the corrected optimizer fixes the total
  constraint, but comparing that corrected optimizer back to the Definition 1
  square-root profile accounts for the extra `T` in the current finite route.

## 5. Source Deviation

The printed finite constant `(T+1)/N` is not what Lean proves
unconditionally. Lean proves the corrected finite bound `(2T+1)/N`, and this
is enough for the paper's asymptotic `1/2`-homogeneity conclusion. The missing
finite type-count shift in the displayed relaxed optimizer is documented as a
source finite-constant deviation, not as an obstacle to the downstream theorem
path.

## 6. Verdict

Proposition 2 is formalized for the paper-facing homogeneity result used
downstream. The exact printed sharp finite constant is retained only as a
documented source-repair target.
