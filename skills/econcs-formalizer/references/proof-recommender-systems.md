# Applications: Recommender Systems

Use for `EconCSLib/Applications/RecommenderSystems/*`, accuracy/diversity,
producer fairness, discretization bias, classwise policies, and count
allocation.

## Accuracy, Diversity, and Count Allocation

- Split recommendation diversity/homogeneity proofs into three layers: finite
  exchange or first-order conditions forcing pairwise count balance; a generic
  representation lemma converting count error to share/homogeneity error; and
  the asymptotic or order-statistic layer.
- For symmetric i.i.d. Bernoulli items, the finite balance proof should cancel
  the common positive likelihood-success coefficient and use strict
  antitonicity of `(1 - q)^k` under `0 < q < 1`.
- For uniform `[0,1]`, `k = 1` recommendation values, use the closed form
  `1 - 1 / (q + 1)` for the expected maximum of `q` samples. Its forward
  marginal is `1 / ((q + 1) * (q + 2))`; the positive-count backward marginal is
  `1 / (q * (q + 1))`.
- For square-root homogeneity, separate exact marginal algebra, a target-profile
  representation bridge, and the real-relaxation/integer-rounding theorem.
- For separable objectives, discharge exchange certificates by showing
  likelihoods are a positive scale times squared shifted targets and anchors
  bracket those targets.
- For finite fixed-total count-allocation optimization, encode allocations as
  functions into `Fin (N + 1)` plus a total-sum proof, optimize over that finite
  code space, then decode to the paper allocation type.

## Policy and Fairness Layers

- For finite fair-division allocation theorems in recommender settings, first
  prove the theorem for an abstract marginal bound. Then add a paper-facing
  corollary instantiating the bound as the finite maximum one-good marginal
  value.
- For symmetry/type-reduction arguments, prove weighted sums by type-cardinality
  equal sums over original agents, and finite minima over agents equal finite
  minima over types when representatives witness every fiber.
- For baseline constrained problems at `gamma = 0`, reduce the constraint to
  nonnegativity when objectives are normalized nonnegative utilities. Witness
  nonemptiness with an arbitrary default policy.

## Discretization Bias

- Prove the actual paper-level continuous/probability theorem when requested;
  do not silently replace it with a finite adaptation. Use finite wrappers only
  as intermediate algebra when they are explicitly connected back to the paper
  statement.
- Keep finite expected-objective bridges generic: deterministic objective,
  expected objective, monotone/linear expectation interface, then paper-facing
  theorem.
- If row-wise Bayes or conditional distribution identities are still assumed,
  name those assumptions in the theorem and README exactly; do not mark the
  source theorem fully formalized until they are instantiated from the model.
