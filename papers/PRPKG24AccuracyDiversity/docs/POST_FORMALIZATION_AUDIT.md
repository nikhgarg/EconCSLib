# Post-Boundary Formalization Audit

## Scope

This audit records the detailed PRPKG boundary after the latest proof pass. The
human-facing status entrypoint is `FINAL_VALIDATION_REPORT.md`. PRPKG is
recorded as formalized. Proposition 4's concrete continuous-sphere endpoint is
proved: Lean checks the unit-sphere model, normalized uniform measure,
radial-kernel symmetry, integrability, compact-max, and positive-Laplace-defined
objective route. The continuity/Gamma regularity interpretation is recorded as
a validation note rather than an open formalization caveat.

Source version: The ACM Web Conference, 2024, pp. 1318--1329,
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
| Definition 1 | formalized | Equation (5) is closed for finite real `gamma`; the `gamma = infinity` bullet is closed as the complete-homogeneity profile concentrated on a chosen likelihood maximizer. |
| Definition 2 | formalized | Equation (6) sequence homogeneity is exposed directly. |
| Definition 3 | formalized | Expected order-statistic mean interface and top-`k` oracle bridge are closed. |
| Theorem 1(i)-(v) | formalized | Finite-discrete, bounded, exponential, Pareto, and all-consumed/common-mean branches are closed. |
| Corollary 1 | formalized | Concrete witnesses cover every `gamma >= 0` case. |
| Proposition 2 | formalized | The homogeneity conclusion is closed via the corrected finite `(2m+1)/N` bound; see the source-deviation note below. |
| Corollary 3 | formalized | i.i.d. Bernoulli `0`-homogeneity endpoint is closed. |
| Theorem 2(i)-(iv) | formalized | Top-one regimes and all-consumed argmax interpretation are closed. |
| Theorem 3 | formalized | Varying-success log-share limit and all-consumed argmax endpoint are closed. |
| Proposition 4 | formalized | Concrete sphere, normalized Haar-uniform profile, radial log-kernel symmetry, compact maximizer, integrability, and positive-Laplace-defined objective route are closed. Validation note: the endpoint exposes the radial-kernel continuity regularity used to read the displayed `Gamma` limit as the formal compact-supremum objective. |
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

`DependencyDAG.tex` uses source-named nodes and has been updated so Definition
1's `gamma = infinity` clause and Proposition 4's concrete
sphere/Laplace-defined endpoint are green. The source-regularity/Gamma
interpretation is represented as a validation note, not as missing sphere,
uniform-measure, Fubini, or Laplace machinery.

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
  arguments. Proposition 4 now has a concrete paper-local sphere instantiation;
  a reusable version would still be useful if another continuous geometric
  paper needs the same pattern.

No additional library move was made in this audit pass: the current PRPKG code
is already using the shared library for the reusable primitives that have
stabilized, and the remaining candidates require broader API design.

## Validation Commands

The closeout pass ran:

```bash
lake build PRPKG24AccuracyDiversity
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --statement-check
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --assumption-check
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --precheck
python3 scripts/sync_paper_status.py
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py --paper PRPKG24AccuracyDiversity --paper-closeout --include-active --info-limit 0
python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0
git diff --check
```

The targeted paper-closeout repository audit passes with no PRPKG-specific
errors or warnings. The broader unfiltered repository audit still has unrelated
maintenance findings, including a pre-existing tracked source-PDF artifact in
`papers/GLM20DroppingStandardizedTesting`.

`DependencyDAG.pdf` was written from `papers/PRPKG24AccuracyDiversity` with
`pdflatex`, but MiKTeX exits with code 134 after trying to write user
config/log files under read-only `~/.miktex`. `mutool draw` was used instead
for PNG rendering and visual inspection; the rendered DAG has no node/text
overlap after the Definition 1 infinite-profile and Proposition 4
duplicate-node fixes.
