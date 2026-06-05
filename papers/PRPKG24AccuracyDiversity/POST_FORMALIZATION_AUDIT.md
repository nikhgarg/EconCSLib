# Post-Boundary Formalization Audit

## Scope

This audit records the current PRPKG boundary after the latest proof pass.
PRPKG is still a partial formalization because the full Proposition 4
continuous-sphere/Laplace layer remains open. The boundary is otherwise closed
for the paper-facing results listed in `PaperInterface.lean`.

Source version: WWW '24 / The ACM Web Conference 2024, pp. 1318--1329,
DOI `10.1145/3589334.3645625`; the local source cache is arXiv:2307.15142v1.
This checkout has the extracted source text cache `PRPKG24AccuracyDiversity.txt`;
the ignored PDF cache `PRPKG24AccuracyDiversity.pdf` is not present locally and
should be recreated from arXiv only when fresh PDF-line inspection is needed.

## Named Source Inventory

The cached text contains the following named source items covered by the
paper-local review surface:

| Source item | Current status | Notes |
|---|---|---|
| Example 1 | formalized | Calibration/log-relaxation and harmonic sequence endpoints are closed. |
| Definition 1 | formalized with caveat | Equation (5) is closed for finite real `gamma`; the `gamma = infinity` bullet is treated as an intuitive limit note. |
| Definition 2 | formalized | Equation (6) sequence homogeneity is exposed directly. |
| Definition 3 | formalized | Expected order-statistic mean interface and top-`k` oracle bridge are closed. |
| Theorem 1(i)-(v) | formalized | Finite-discrete, bounded, exponential, Pareto, and all-consumed/common-mean branches are closed. |
| Corollary 1 | formalized | Concrete witnesses cover every `gamma >= 0` case. |
| Proposition 2 | formalized | The homogeneity conclusion is closed via the corrected finite `(2m+1)/N` bound; see the source-deviation note below. |
| Corollary 3 | formalized | i.i.d. Bernoulli `0`-homogeneity endpoint is closed. |
| Theorem 2(i)-(iv) | formalized | Top-one regimes and all-consumed argmax interpretation are closed. |
| Theorem 3 | formalized | Varying-success log-share limit and all-consumed argmax endpoint are closed. |
| Proposition 4 | conditional | Averaging/kernel symmetry minimization checkpoint is closed; the literal sphere/Fubini/Laplace analytic layer remains open. |
| Proposition 5 | formalized | Top-`k` order-statistic identity and uniform instance are closed. |
| Lemma 1 | formalized | Bounded-support top-`k` asymptotic is closed through reflected-CDF and tail-mass routes. |
| Lemma D.1 | formalized | Optimizer-limit content used downstream is closed; the printed sign issue is recorded below. |
| Lemma D.2 | formalized | Bounded-tail integral asymptotic route is closed. |
| Lemma D.3 | formalized | Exponential order-statistic/top-`k` finite oracle route is closed. |
| Lemma D.4 | formalized | Pareto order-statistic/gamma-ratio route is closed. |
| Lemma D.5 | formalized | Integer/real rounding route needed downstream is closed. |

## Source-Deviation Notes

Proposition 2: Lean proves a corrected finite statement with error
`(2m+1)/N` and derives the asymptotic `1/2`-homogeneity conclusion from that
bound. The PDF's displayed relaxed optimizer sums to `N-m`; the corrected
normalization used in Lean sums to `N`. The printed sharper finite constant
`(m+1)/n` is therefore recorded as a finite-constant source deviation. It does
not affect any downstream result currently claimed by the paper interface.

Lemma D.1: the literal printed part (i) has a sign mismatch (`B > 0`,
`sigma < 0`) relative to the proof and to the later Theorem 1(i) exponential
decay application. Lean closes the optimizer-limit content and downstream
Theorem 1 routes directly under the source-appropriate positive-rate or decay
conventions. The sign issue is documented as a source note rather than a
remaining formalization target.

Theorem 2(iv): Lean interprets the paper's limiting `1/0` homogeneity statement
as the likelihood-argmax endpoint for the all-consumed `alpha = 0` case, which
is the natural and source-consistent interpretation. This is a proof-route note,
not a theorem caveat.

## DAG Audit

`DependencyDAG.tex` uses source-named nodes. The only non-green named result
node is full Proposition 4. The separate Proposition 4 checkpoint node is green
because Lean has closed the reusable averaging/kernel-symmetry minimization
step; the red conditional node records the remaining literal continuous sphere,
uniform-measure, Fubini, and Laplace-principle layer.

No green node depends by a solid edge on a red/yellow node. D.1 and D.5 are
green, with the source-quality notes recorded in this report rather than as DAG
caveat statuses.

## Human Review Surface

`PaperInterface.lean` exposes 27 human-review rows. These are paper-facing rows,
not an implementation ledger:

- Definition 1, Definition 2, Definition 3, and Example 1.
- Theorem 1(i), Theorem 1(ii), Theorem 1(iii), Theorem 1(iv), and the two
  Theorem 1(v) all-consumed endpoints.
- Corollary 1, Theorem 2(i), Theorem 2(ii), Theorem 2(iii), the two Theorem
  2(iv) endpoints, Theorem 3, and Corollary 3.
- Proposition 2, Proposition 4, Proposition 5, Lemma 1, and Lemmas D.1-D.5.

Auxiliary certificate structures, finite analogues, source-repair seams, and
long proof-interface declarations are intentionally excluded from this count and
remain in `ProofInterface.lean` or the implementation files.

## Library Extraction Review

Already-elevated reusable infrastructure used by this proof includes:

- `EconCSLib/Applications/RecommenderSystems/AllocationSequence.lean` for
  simplex optimizer-limit and allocation-sequence convergence tools.
- `EconCSLib/Applications/RecommenderSystems/TopKOracle.lean` for top-`k`
  value/oracle interfaces and scaled-marginal certificates.
- `EconCSLib/Foundations/Math/FiniteRounding.lean` for no-crossing finite
  rounding tools.
- `EconCSLib/Foundations/Math/GammaAsymptotics.lean` for gamma-ratio
  asymptotics and finite envelopes.
- `EconCSLib/Foundations/Probability/OrderStatistics.lean`,
  `RealDistribution.lean`, `Exponential.lean`, `Pareto.lean`, and
  `Symmetry.lean` for reusable order-statistic, product-measure, exponential,
  Pareto, reflected-CDF, and symmetry/Fubini infrastructure.

Further extraction candidates are documented but not moved in this pass:

- A generic apportionment/divisor-method rounding theorem for separable
  concave objectives, motivated by Proposition 2's corrected finite constant.
  This would be useful if another recommendation or allocation paper needs
  sharp finite coordinate bounds, but it is not needed for the current
  asymptotic boundary.
- A compact-group/Haar-measure action layer for sphere or manifold symmetry
  arguments. This belongs in the library once Proposition 4 or another
  continuous geometric paper needs the concrete sphere instantiation.
- A reusable Laplace-principle scaffold for continuous heavy EconCS papers.
  This should be designed together with other large-deviation/Laplace papers
  rather than hidden inside PRPKG.

No additional library move was made in this audit pass: the current PRPKG code
is already using the shared library for the reusable primitives that have
stabilized, and the remaining candidates require broader API design.

## Commands

The closeout pass ran:

```bash
lake env lean papers/PRPKG24AccuracyDiversity/MainTheorems.lean
lake build PRPKG24AccuracyDiversity
python3 scripts/sync_paper_status.py
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py
git diff --check
```

The DAG was rendered from `papers/PRPKG24AccuracyDiversity` with `pdflatex` and
visually inspected from a PNG conversion.
