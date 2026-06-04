# Validation Report: PRPKG Theorem 2

## 1. Source and Scope

- Paper: *Reconciling the accuracy-diversity trade-off in recommendations*
- Source version: arXiv:2307.15142v1, cached locally as `PRPKG24AccuracyDiversity.pdf`
- Lean folder: `papers/PRPKG24AccuracyDiversity`
- Human-facing theorem file: `MainTheorems.lean`
- Proof files: `DecayingBernoulli.lean`, `SeparableAsymptotic.lean`, `TailHomogeneity.lean`
- DAG artifacts: `DependencyDAG.tex`, `DependencyDAG.pdf`
- Scope of this report: Theorem 2 only. This is not a final validation report for the whole paper.

## 2. Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Theorem 2(i), top-one `α = 0` | `paper_theorem2_i_decaying_bernoulli_top_one_alpha_zero_sequence_uniform_homogeneity` | fully formalized | exact under explicit probability assumptions | Reduces to the existing i.i.d. Bernoulli uniform-homogeneity theorem. |
| Theorem 2(i), top-one `0 < α < 1` | `paper_theorem2_i_decaying_bernoulli_top_one_subunit_sequence_uniform_homogeneity` | fully formalized | exact under explicit probability assumptions | Uses the paper's product-tail strategy through the concrete schedule `ε_N = (N+1)^((α-1)/2)`. |
| Theorem 2(ii), top-one `α = 1` | `paper_theorem2_ii_decaying_bernoulli_top_one_alpha_one_sequence_homogeneity` | fully formalized | minor proof-route deviation | Uses a real-`c` harmonic-log product bound plus reverse-order correction and `ε_N = (N+1)^(-1/4)`. |
| Theorem 2(iii), top-one `α > 1` | `paper_theorem2_iii_decaying_bernoulli_top_one_superunit_sequence_homogeneity` | fully formalized | minor proof-route deviation | Uses weights `p_t^(1/α)`, raw/reverse product bridges, and `ε_N = (N+1)^(-(α-1)/(2*(α+1)))`. |
| Theorem 2(iv), all-consumed `α > 0` | `paper_theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_sequence_homogeneity` | fully formalized | stronger route than paper | Finite FOC gives bounded scaled counts directly, implying the `1/α`-homogeneity limit. |
| Theorem 2(iv), all-consumed `α = 1` | `paper_theorem2_iv_decaying_bernoulli_all_consumed_alpha_one_sequence_homogeneity` | fully formalized | exact special case | Specialized wrapper for the paper's common `α = 1` target. |
| Theorem 2(iv), all-consumed `α = 0` | `paper_theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax_optimum` | fully formalized | intended degenerate interpretation | Lean interprets the limiting `1/0`-homogeneity statement as the likelihood-argmax endpoint, which is the meaningful all-consumed limit of the paper's positive-`α` formula. |

## 3. Additional Assumptions Beyond Paper

- Top-one branches require explicit nondegenerate probability-validity assumptions: `0 < c`, `0 ≤ d`, `decayingBernoulliSuccess c d α 0 < 1`, and `∀ t, 0 < likelihood t`.
- The `α = 0` top-one wrapper uses `0 < c` and `c < 1`, matching the constant Bernoulli success probability needed by the i.i.d. Bernoulli theorem.
- All-consumed positive-`α` wrappers require `0 < α`, `0 < c`, `0 ≤ d`, and `∀ t, 0 < likelihood t`.

## 4. Proof-Strategy Deviations

- The `α = 1` top-one proof avoids the paper's displayed finite telescope unless `c` is an integer. Lean proves a real-`c` harmonic-log route instead, then adds the reverse-order correction needed for nonuniform target weights.
- The `α > 1` top-one proof uses an explicit continuous asymptotic schedule and two limit lemmas, `N(ε_N N)^(-α) → 0` and `N^2(ε_N N)^(-(α+1)) → 0`, to control the inverse-survival correction.
- The all-consumed proof is simpler and stronger than the paper's scalar sum-asymptotic route: it derives a finite pairwise scaled-count bound from the FOC.

## 5. Conditional Results and Remaining Gaps

- No certificate assumptions remain in the closed Theorem 2 wrappers listed above.
- The paper's broad `α ≥ 0` wording for the all-consumed `1/α` target is read at `α = 0` as the likelihood-argmax endpoint. Lean closes the positive-`α` theorem, exposes `α = 1` separately, and proves this `α = 0` interpretation directly.
- The broader PRPKG paper still has open results outside Theorem 2, tracked in `README.md`.

## 6. Suspected Paper Errors or Inconsistencies

- None found in Theorem 2's statement after making probability-validity and positive-likelihood assumptions explicit.
- Separate from Theorem 2, Proposition 2's printed relaxed optimizer appears to omit a `+m` normalization shift; that issue remains documented in `README.md`.

## 7. Verdict

- Completion status for Theorem 2: complete under the explicit nondegeneracy assumptions above.
- The Lean development verifies all top-one regimes, the all-consumed positive-`α` branch, and the all-consumed `α = 0` argmax interpretation, with no `sorry` or certificate hypothesis left in the closed source-facing wrappers.
