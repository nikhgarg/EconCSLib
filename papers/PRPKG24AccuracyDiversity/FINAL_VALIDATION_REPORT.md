# Final Validation Report: PRPKG24 Accuracy-Diversity

## 1. Human Verdict

- Lean formalization status: partially formalized
- Human dashboard review status: 0/27 rows reviewed; 0 stale; 0 mismatches.
- Human summary: Proposition 2's printed finite bound appears to miss a factor of 2; Lean proves the corrected finite bound, which is sufficient for the asymptotic 1/2-homogeneity result. Fully formalizing the remaining result, Proposition 4, requires a general Laplace-principle-related analysis library.

- Lean formalization status: partially formalized.
- Human dashboard review status: 0 reviewed rows, 0 stale rows, 0 mismatch rows, 27 total rows.
- Paper correctness verdict: the current Lean surface supports the main closed routes; Proposition 2's printed finite constant and Lemma D.1(i)'s printed sign convention are documented source deviations.
- Qualitative proof verdict: all main theorem and downstream asymptotic routes are closed except Proposition 4's continuous-sphere analytic layer.
- Lean footprint: 138 `PaperInterface.lean` LOC, 27 review rows.

## 2. Source and Scope

- Paper: *Reconciling the Accuracy-Diversity Trade-off in Recommendations*.
- Publication venue: WWW '24 / The ACM Web Conference 2024.
- Source version: WWW '24 proceedings metadata plus arXiv:2307.15142v1 source cache.
- Lean folder: `papers/PRPKG24AccuracyDiversity`.
- Human-facing theorem file: `papers/PRPKG24AccuracyDiversity/PaperInterface.lean`.
- Detailed post-boundary audit: `papers/PRPKG24AccuracyDiversity/POST_FORMALIZATION_AUDIT.md`.
- DAG artifacts: `papers/PRPKG24AccuracyDiversity/DependencyDAG.tex`, `papers/PRPKG24AccuracyDiversity/DependencyDAG.pdf`.

## 3. What Has Been Proven

The current proof closes Example 1, Definitions 1-3, Theorems 1-3, Corollaries
1 and 3, Proposition 2's corrected finite/asymptotic homogeneity route,
Proposition 5, Lemma 1, and Lemmas D.1-D.5 at the paper-facing
`PaperInterface.lean` endpoints.

Proposition 4 has a closed averaging/kernel-symmetry minimization checkpoint.
The remaining literal source gap is the continuous sphere profile space,
uniform measure, cosine-kernel/Fubini/symmetry, and Laplace analytic
instantiation needed for the full source proposition.

## 4. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| abbrev definition1 | `definition1` | Definition 1 (γ-homogeneity). A set S is γ-homogeneous if for all t ∈ [m], pγ rt (S) = Pmt γ. i=1 pi (5) γ-homogeneity captures several intuitive notions of diversity, using p1 , · · · , pm as a benchmark: 1 The mathematical result in th... |
| abbrev definition2 | `definition2` | Definition 2 (γ-homogeneity for set sequences). A sequence of sets {Sn }∞ n=1 is γ-homogeneous if for all t ∈ [m], pγ (6) lim rt (Sn ) = Pmt γ . n→∞ i=1 pi One perhaps surprising aspect of our results is that γ-homogeneity is sufficient... |
| abbrev definition3 | `definition3` | Definition 3. Define µD (i, a) to be the expected value of the i-th order statistic2 of a random variables drawn i.i.d. from D. (Thus, µD (1, a) is the expected minimum of a i.i.d. draws from D and µD (a, a) is the expected maximum.) The... |
| abbrev example1 | `example1` | - Example 1: exact calibrated top-one exponential sequence. |
| abbrev theorem1_i | `theorem1_i` | Theorem 1. Suppose Xi ∼ D where D has finite mean. Then the following statements hold. (i) [Finite Discrete] If D is a finite discrete distribution, {Sn,k }∞ n=1 is 0-homogeneous. (ii) [Bounded] If D has support bounded from above by M w... |
| abbrev theorem1_ii | `theorem1_ii` | Theorem 1. Suppose Xi ∼ D where D has finite mean. Then the following statements hold. (i) [Finite Discrete] If D is a finite discrete distribution, {Sn,k }∞ n=1 is 0-homogeneous. (ii) [Bounded] If D has support bounded from above by M w... |
| abbrev theorem1_iii | `theorem1_iii` | Theorem 1. Suppose Xi ∼ D where D has finite mean. Then the following statements hold. (i) [Finite Discrete] If D is a finite discrete distribution, {Sn,k }∞ n=1 is 0-homogeneous. (ii) [Bounded] If D has support bounded from above by M w... |
| abbrev theorem1_iv | `theorem1_iv` | Theorem 1. Suppose Xi ∼ D where D has finite mean. Then the following statements hold. (i) [Finite Discrete] If D is a finite discrete distribution, {Sn,k }∞ n=1 is 0-homogeneous. (ii) [Bounded] If D has support bounded from above by M w... |
| abbrev theorem1_v_common_mean | `theorem1_v_common_mean` | Theorem 1. Suppose Xi ∼ D where D has finite mean. Then the following statements hold. (i) [Finite Discrete] If D is a finite discrete distribution, {Sn,k }∞ n=1 is 0-homogeneous. (ii) [Bounded] If D has support bounded from above by M w... |
| abbrev theorem1_v_unique_common_mean | `theorem1_v_unique_common_mean` | Theorem 1. Suppose Xi ∼ D where D has finite mean. Then the following statements hold. (i) [Finite Discrete] If D is a finite discrete distribution, {Sn,k }∞ n=1 is 0-homogeneous. (ii) [Bounded] If D has support bounded from above by M w... |
| abbrev corollary1 | `corollary1` | Corollary 1. For any γ ≥ 0, there exists D such that when Xi homogeneous. ∼ D and k is fixed, {Sn,k }∞ n=1 is γ- Intuitively, heavy-tailed distributions (part (iv)) induce less diverse recommendations since the marginal returns of recomm... |
| abbrev theorem2_i | `theorem2_i` | Theorem 2 (Decaying success probabilities). Suppose that Xi ∼ Ber(qi ) are i.i.d. Bernoulli random (t) variables such that qi = c(i + d)−α for all i ≥ 1 and some α, c, d ≥ 0. Then the following statements hold. (i) {Sn,1 }∞ n=1 is 0-homo... |
| abbrev theorem2_ii | `theorem2_ii` | Theorem 2 (Decaying success probabilities). Suppose that Xi ∼ Ber(qi ) are i.i.d. Bernoulli random (t) variables such that qi = c(i + d)−α for all i ≥ 1 and some α, c, d ≥ 0. Then the following statements hold. (i) {Sn,1 }∞ n=1 is 0-homo... |
| abbrev theorem2_iii | `theorem2_iii` | Theorem 2 (Decaying success probabilities). Suppose that Xi ∼ Ber(qi ) are i.i.d. Bernoulli random (t) variables such that qi = c(i + d)−α for all i ≥ 1 and some α, c, d ≥ 0. Then the following statements hold. (i) {Sn,1 }∞ n=1 is 0-homo... |
| abbrev theorem2_iv_positive_alpha | `theorem2_iv_positive_alpha` | Theorem 2 (Decaying success probabilities). Suppose that Xi ∼ Ber(qi ) are i.i.d. Bernoulli random (t) variables such that qi = c(i + d)−α for all i ≥ 1 and some α, c, d ≥ 0. Then the following statements hold. (i) {Sn,1 }∞ n=1 is 0-homo... |
| abbrev theorem2_iv_alpha_zero | `theorem2_iv_alpha_zero` | Theorem 2 (Decaying success probabilities). Suppose that Xi ∼ Ber(qi ) are i.i.d. Bernoulli random (t) variables such that qi = c(i + d)−α for all i ≥ 1 and some α, c, d ≥ 0. Then the following statements hold. (i) {Sn,1 }∞ n=1 is 0-homo... |
| abbrev theorem3 | `theorem3` | Theorem 3 (Varying success probability across types). Suppose that for each fixed t, Xi i.i.d. Bernoulli random variables. Then lim rt (Sn,1 ) ∝ n→∞ log 1−q t ∼ Ber(qt ) are (9) while Sn,n contains only items of type t = arg maxt∈[m] pt... |
| abbrev corollary3 | `corollary3` | Corollary 3 (Conditional item values are i.i.d. Bernoulli). When Xi 0-homogeneous. ∼ Ber(q) for q > 0, then Sn,1 is Therefore, if the success probability is the same for all items, optimal solutions are 0-homogeneous (each item is equall... |
| abbrev proposition2 | `proposition2` | Proposition 2. When Xi ∼ U ([0, 1]), √ pt rt (Sn,k ) − Pm √ i=1 pi ≤ m+1 . n (8) √ p for all k ≤ Pm m√pi n − m − 1. i=1 Therefore, for any n, Sn,k is approximately 21 -homogeneous. In addition, for any k that is smaller than a constant f... |
| abbrev proposition4 | `proposition4` | Proposition 4. Consider a non-constant function p(u, v) : Sd × Sd → (0, 1], interpreted as the probability that item v does not satisfy a user with preference u, such that p(u, v) = q(∥u − v∥) can be expressed as a function of the cosine... |
| abbrev proposition5 | `proposition5` | Proposition 5. For Xi ∼ D, min{k,a} h(a) = X i=1 µD (a − i + 1, a). (78) Recall that µD (i, a) is the expected value of the i-th order statistic of a random variables drawn i.i.d. from D. |
| abbrev lemmaD1 | `lemmaD1` | - Lemma D.1: optimizer sequence limit from the appendix compactness/unique-limit objective route. |
| abbrev lemmaD2 | `lemmaD2` | - Lemma D.2: bounded-tail integral asymptotic. |
| abbrev lemma1 | `lemma1` | Lemma 1. If D has support bounded from above by M with pdf fD such that limx→M (Mf−x) β−1 = c for some β, c > 0, then lima→∞ M k−h(a) = 1. −1 Ba β Combining Lemma 1 with Lemma D.1(ii), with σ = − β1 , we show that for D as in Theorem 1(i... |
| abbrev lemmaD3 | `lemmaD3` | - Lemma D.3: exponential order-statistic sequence formula. |
| abbrev lemmaD4 | `lemmaD4` | - Lemma D.4: concrete iid Pareto order-statistic sequence formula. |
| abbrev lemmaD5 | `lemmaD5` | - Lemma D.5: real-to-integer rounding bridge. |
<!-- lean-derived-definitions:end -->

## 5. Named Theorem Statements Checked

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

None exposed in the current dashboard surface.
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| abbrev corollary1 | `corollary1` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev corollary3 | `corollary3` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev definition1 | `definition1` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev definition2 | `definition2` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev definition3 | `definition3` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:54Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:54Z): The draft exposes the oracle type name but does not spell out the order-statistic/value-oracle content of Definition 3. |
| abbrev example1 | `example1` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma1 | `lemma1` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemmaD1 | `lemmaD1` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemmaD2 | `lemmaD2` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemmaD3 | `lemmaD3` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemmaD4 | `lemmaD4` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemmaD5 | `lemmaD5` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev proposition2 | `proposition2` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev proposition4 | `proposition4` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev proposition5 | `proposition5` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem1_i | `theorem1_i` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem1_ii | `theorem1_ii` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem1_iii | `theorem1_iii` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem1_iv | `theorem1_iv` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem1_v_common_mean | `theorem1_v_common_mean` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem1_v_unique_common_mean | `theorem1_v_unique_common_mean` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_i | `theorem2_i` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_ii | `theorem2_ii` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_iii | `theorem2_iii` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_iv_alpha_zero | `theorem2_iv_alpha_zero` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_iv_positive_alpha | `theorem2_iv_positive_alpha` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3 | `theorem3` | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:54Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Additional Assumptions Beyond Paper

- Proposition 4 currently stops at an explicit kernel-symmetry checkpoint rather than instantiating the paper's continuous sphere model.
- Auxiliary asymptotic and finite-routing endpoints are certificate-gated when the source proof needs a reusable analytic or rounding boundary.

## 8. Proof-Strategy Deviations

### Source Deviations

- Proposition 2: Lean proves the corrected finite error `(2m+1)/N` and derives the paper's asymptotic `1/2`-homogeneity conclusion. The printed sharper finite constant appears to miss a factor of 2.
- Lemma D.1(i): the printed sign convention conflicts with the proof route and downstream exponential-decay use. Lean closes the downstream routes under the source-appropriate positive-rate/decay conventions.

## 9. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 10. Library Lift Pass

Reusable infrastructure already lives in shared recommender, finite-rounding,
asymptotics, order-statistics, exponential, Pareto, real-distribution, and
symmetry modules. Remaining candidates for future library work are generic
separable concave apportionment rounding, compact-group/Haar action APIs, and a
continuous Laplace-principle scaffold.

## 11. DAG Audit

The DAG records the paper-facing theorem boundary. Full Proposition 4 remains
non-green; the separate averaging/kernel checkpoint is green and should not be
read as closing the continuous sphere/Laplace source layer.

## 12. Conditional Results and Remaining Gaps

None separately recorded in the existing report.

## 13. Suspected Paper Errors or Inconsistencies

None separately recorded in the existing report.

## 14. Validation Checks

The closeout audit records passing checks for `lake build PRPKG24AccuracyDiversity`,
`python3 scripts/sync_paper_status.py --check`, `python3 scripts/audit_repository.py`,
and `git diff --check`.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 27 rows; 26 match, 1 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

Flagged rows:
- `definition3`: uncertain. The draft exposes the oracle type name but does not spell out the order-statistic/value-oracle content of Definition 3.

## 15. Final Verdict

- Completion status: partially formalized.
- Summary: Proposition 2's printed finite bound appears to miss a factor of 2; Lean proves the corrected finite bound, which is sufficient for the asymptotic 1/2-homogeneity result. Fully formalizing the remaining result, Proposition 4, requires a general Laplace-principle-related analysis library.
