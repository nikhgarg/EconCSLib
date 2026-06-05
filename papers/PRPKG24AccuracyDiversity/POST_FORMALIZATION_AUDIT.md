# Post-Boundary Formalization Audit

## Scope

This is the human-facing status note for the current PRPKG partial
formalization boundary. The implementation README is a source-audit/work ledger;
this file is the concise public summary.

Source version: WWW '24 / The ACM Web Conference 2024, pp. 1318--1329,
DOI `10.1145/3589334.3645625`; the local source cache is
arXiv:2307.15142v1. The ignored PDF cache is not present in this checkout and
should be recreated from arXiv only when fresh line-level source inspection is
needed.

## Boundary

PRPKG is partially formalized. All paper-facing rows exposed in
`PaperInterface.lean` are formalized except for the literal continuous
sphere/Laplace-principle layer of Proposition 4.

Closed results without a human-facing caveat are intentionally not listed one by
one here. The review surface has 27 paper-facing rows in `PaperInterface.lean`;
implementation aliases and helper theorem inventories live in
`ProofInterface.lean` and the proof files.

## Caveats And Deviations

- Definition 1: Lean formalizes equation (5) for finite real `gamma`. The
  source's `gamma = infinity` bullet is treated as an intuitive limiting case,
  not as a finite-real definition.
- Proposition 2: the printed finite bound appears to miss a factor of 2. Lean
  proves the corrected finite bound with error `(2m+1)/N`, which is sufficient
  for the asymptotic `1/2`-homogeneity result used downstream.
- Theorem 2(iv): Lean interprets the source's limiting `1/0` homogeneity phrase
  as the likelihood-argmax endpoint for the all-consumed `alpha = 0` case. This
  is the intended source reading and not a theorem caveat.
- Lemma D.1: the printed part (i) has a sign mismatch (`B > 0`, `sigma < 0`)
  relative to the proof and later Theorem 1(i) usage. Lean closes the downstream
  optimizer-limit routes under the source-appropriate positive-rate/decay
  conventions.
- Lemma D.4: the arXiv TeX confirms the Pareto target uses the denominator
  `B * a^(1/alpha)` where needed; a later proof line prints `B log a`. Lean
  follows the Pareto-consistent theorem target.
- Proposition 4: the reusable averaging/kernel-symmetry minimization checkpoint
  is formalized, but the literal sphere profile space, uniform measure,
  cosine-kernel/Fubini layer, and Laplace-principle analytic certificate remain
  outside the current boundary.

## DAG Status

`DependencyDAG.tex` uses source-named nodes. The only non-green named-result
node is full Proposition 4. The separate Proposition 4 checkpoint node is green
because Lean closes the reusable averaging/kernel-symmetry minimization step.

No green node depends by a solid edge on a red or yellow node. Source-quality
notes for Proposition 2, Lemma D.1, and Lemma D.4 are recorded above rather than
shown as DAG caveat statuses, because the downstream formalized results do not
depend on the printed erroneous forms.

## Validation

The closeout pass rebuilt `PRPKG24AccuracyDiversity`, checked the generated
status tables, ran the repository audit, checked whitespace, and rendered and
visually inspected the dependency DAG. The repository audit had no errors; its
remaining warnings were the expected public-release missing-PDF/review-cache
warnings.

## Future Library Work

Fully formalizing Proposition 4 should be done through shared analysis
infrastructure rather than paper-local assumptions: a sphere/Haar-style symmetry
layer, Fubini/kernel integration tools, and a general Laplace-principle-related
analysis library.
