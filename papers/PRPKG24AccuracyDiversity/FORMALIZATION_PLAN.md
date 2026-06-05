# PRPKG24 Formalization Plan

This public folder tracks the partial formalization of Peng, Raghavan,
Pierson, Kleinberg, and Garg, "Reconciling the Accuracy-Diversity Trade-off in
Recommendations" (arXiv:2307.15142v1).

## Current Boundary

- Formalized: the paper-facing definitions, Example 1, Theorems 1-3,
  Corollaries 1 and 3, Proposition 5, Lemma 1, Appendix Lemmas D.1-D.5, and
  the corrected finite/asymptotic route for Proposition 2.
- Remaining: Proposition 4's continuous sphere averaging/Laplace-principle
  analytic certificate.
- Source deviations: Proposition 2's printed finite bound appears to miss a
  factor of 2/type-count shift; Lean proves the corrected finite bound needed
  for the asymptotic 1/2-homogeneity conclusion. Lemma D.1(i)'s printed sign
  convention is documented as nonblocking for downstream uses.

## Reusable Library Surface

The proof currently uses reusable infrastructure in:

- `EconCSLib.Foundations.Math`: finite sums, rounding, binomial bounds,
  asymptotic error envelopes, power comparisons, and gamma/beta asymptotics.
- `EconCSLib.Foundations.Probability`: order-statistic interfaces, real
  distribution lemmas, Bernoulli/Pareto/exponential helpers, averaging and
  symmetry certificates, and large-deviation weighted-sum helpers.
- `EconCSLib.Applications.RecommenderSystems`: finite allocations,
  allocation sequences, and top-k oracle bridges.

## Next Work

The next proof target is Proposition 4. The expected reusable prerequisite is
a general Laplace-principle-related analysis layer for continuous sphere
integrals and asymptotic concentration. Once that library layer is available,
the remaining paper work should connect it to the existing Proposition 4
averaging/kernel checkpoints in `ContinuousSphere.lean`.
