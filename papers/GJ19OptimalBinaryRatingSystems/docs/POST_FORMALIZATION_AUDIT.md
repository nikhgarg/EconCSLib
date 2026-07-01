# Post-Formalization Audit: GJ19 Optimal Binary Rating Systems

## Scope

This audit records the closeout state for *Designing Optimal Binary Rating
Systems*. The formalized source is the AISTATS 2019 / PMLR 89 paper plus its
PMLR supplement. The human-facing validation entrypoint is
`FINAL_VALIDATION_REPORT.md`.

Current status: formalized. The finite/discrete binary-rating layer, Theorem
3.1 value/rate decomposition, Lemma C.3 aggregation, Lemma C.4 rate
characterization, Lemmas C.5-C.12, finite Theorem 3.2 certificate rows,
Appendix B.1 convergence, Appendix B.2/B.3 learning wrappers, Kendall/Spearman
examples, and reusable weighted large-deviation infrastructure all build.

## Named Source Inventory

| Source item | Current status | Notes |
|---|---|---|
| Bernoulli KL and support-safe KL formulas | formalized | `definition_bernoulli_kl_formula`, `definition_bernoulli_kl_top_formula`. |
| Theorem 3.1 adjacent rate formula | formalized | `theorem31_adjacent_binary_rate_formula` and support-safe variant. |
| Lemma 3.1 closed adjacent-rate expression | formalized | Weighted Bernoulli threshold expression and value at the common threshold are derived. |
| Lemma 3.1 finite equalized optimizer | formalized | Endpoint-aware finite existence/uniqueness/maximin/strict-maximizer certificates are exposed. |
| Finite adjacent objective exact-rate theorem | formalized | Endpoint/source-shaped rows construct the finite adjacent LDP certificates internally. |
| Theorem C.1 weighted skeleton | formalized | Source-facing weighted integral rate skeleton with explicit regularity hypotheses. |
| Lemma C.3 finite and continuum aggregation | formalized | Finite component sums, adjacent dominance, and partition-integral aggregation are checked. |
| Lemma C.4 rate characterization | formalized | Forward and reverse source-facing rate statements are checked. |
| Theorem 3.1 fixed-discretization and continuum branches | formalized | Fixed-discretization rate bridge, `S*` value optimization, and cell-integral branches are checked. |
| Corollary C.2 and Lemmas C.5-C.9 | formalized | Rate/mesh convergence, support bounds, doubled-chain construction, and operation-count support are checked. |
| Theorem 3.2 | formalized | Calculated-grid approximation/runtime certificate rows are checked. |
| Lemmas C.10-C.12 | formalized | Spearman reduction and Kendall/Spearman finite objective optimizers are checked. |
| Theorem B.1 and Corollary C.4 | formalized | Quantile-floor convergence route and equispaced Kendall/Spearman convergence branches are checked. |
| Appendix B.2/B.3 learning lemmas | formalized | Known-type and unknown-type learning wrappers are checked. |
| Empirical and visualization sections | out of Lean scope | Treated as empirical/reproducibility artifacts, not theorem DAG nodes. |

## Agent-Facing Source Notes

The closeout changed the status judgment: the `W - W_k` proof should not be
treated as a caveat. The source proof works with the limiting-gap quantity and
then rewrites it over cross-level cells in the stepwise case. In Lean, keep
the theorem statements source-facing and avoid replacing that object with a
different raw strict-pair complement integral.

Appendix B.1 is also closed for the paper's quantile-floor representation: the
checked theorem
`paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh`
derives the needed selector window from finite optimality and uniform
convergence of the interval-quantile maps. Alternative representatives still
exist as reusable proof-interface routes, but they are not public paper-status
qualifications.

The model-regularity, measurability, boundedness, positivity, and convergence
fields exposed by Lean are ordinary theorem hypotheses. Do not summarize them
as additional assumptions unless a future edit proves that a field is not
derivable from or already present in the source model.

## DAG Audit

`DependencyDAG.tex` uses the shared TikZ preamble and records the AISTATS /
PMLR 89 source. The DAG should show the paper theorem surface as formalized,
with any certificate-style boxes described as formalized certificate rows
rather than open boxes.

Rendered artifact: `DependencyDAG.pdf`. After substantive DAG edits, rerender
from the paper folder and inspect the PDF or PNG conversion for overlap,
stale metadata, missing theorem numbers, and arrowhead direction.

## Human Review Surface

`PaperInterface.lean` is large because it exposes the current finite and
continuum theorem surface, but `status.json` filters the dashboard to
paper-facing rows. Add a dashboard row only when it corresponds to a source
definition, named result, or source-facing theorem component that a human
should review.

Current curated review surface: 25 dashboard rows. The full proof surface is
documented in `FINAL_VALIDATION_REPORT.md`, while source-condition reducers are
kept in `Assumptions.lean` and this audit note rather than counted as public
dashboard assumptions.

## Library Extraction Review

Reusable infrastructure used or added by this pass:

- `EconCSLib.Foundations.Probability.FiniteRatingComparison` for finite
  rating LDP/rating-certificate interfaces.
- `EconCSLib.Foundations.Probability.BinaryRatingLDP` for paper-neutral
  Bernoulli binary-rating rates, endpoint split identities, and weighted
  threshold-rate transformations.
- `EconCSLib.Foundations.Probability.LargeDeviations` for exponential-rate
  certificates and finite aggregation.
- `EconCSLib.Foundations.Probability.IntegralLargeDeviations` for integral
  exponential bounds and weighted Laplace-style skeletons.
- `EconCSLib.Foundations.Probability.FiniteMeasurablePartition` for finite
  partition aggregation of weighted positive kernels.
- `EconCSLib.Foundations.Math.ExponentialBounds` for reusable exponential/log
  algebra.
- `EconCSLib.Foundations.Math.UniformConvergence` for source-style
  uniform-anchor/mesh arguments.

Future extraction candidates:

- generic positive-weight near-minimizer constructors from common
  positivity/continuity assumptions;
- a reusable executable nested-bisection correctness theorem;
- more paper-neutral continuum discretization and monotone partition
  optimization interfaces.

## Commands

Current validation target:

```bash
lake build GJ19OptimalBinaryRatingSystems
```

Status synchronization target:

```bash
python3 scripts/sync_paper_status.py --check
```

Targeted closeout audit:

```bash
python3 scripts/audit_repository.py --paper GJ19OptimalBinaryRatingSystems --paper-closeout --include-active --info-limit 0
```
