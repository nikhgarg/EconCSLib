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
- For decaying Bernoulli all-consumed objectives, keep the generic ranked
  Bernoulli value/marginal layer separate from the paper-specific decay
  sequence. For every positive `α`, the FOC can be stronger than the paper's
  scalar sum-asymptotic route: cancel the positive scale, convert inverse-power
  marginal comparisons into bounded scaled counts `a_t / p_t^(1/α)`, then use a
  generic pairwise-scaled count bridge for exact `C/N` homogeneity. Treat
  `α = 0` and `c = 0` explicitly; the paper-style `1/α` target and objective
  can degenerate there.
- For asymptotic recommendation homogeneity, an `O(1)` pairwise scaled-count
  bound is stronger than necessary. If finite FOCs plus tail/product
  asymptotics give `|a_i/w_i - a_j/w_j| ≤ ε_N N` with `ε_N → 0`, use a
  sublinear pairwise-scaled bridge to get the γ-profile limit.
- When the product/tail estimate is naturally one-sided, use the FOC-to-
  sublinear bridge: prove that any scaled-count gap larger than `ε_N N` makes
  the source backward marginal strictly smaller than the destination forward
  marginal. The finite FOC rules out the gap, and the sublinear scaled-count
  bridge gives the sequence limit.
- For decaying Bernoulli top-one objectives, check `α = 0` before doing product
  asymptotics: rank success probabilities become constant, so the model should
  reduce to the existing i.i.d. Bernoulli satisfaction model and reuse its
  uniform-homogeneity theorem.
- For positive-`α` decaying Bernoulli top-one objectives, first prove count
  divergence of finite optima. The decay probability tends to zero, so a large
  source count has last-item marginal below any fixed destination-count
  marginal; a finite pairwise/fixed-floor threshold plus the FOC rules out
  destinations at or below that floor for large totals.
- After count divergence, separate the raw product estimate from finite
  optimization. Use a floor-aware eventual product certificate: prove that
  beyond a fixed count floor and eventually in `N`, any scaled-count gap larger
  than `ε_N N` makes the top-one source backward marginal strictly smaller
  than the destination forward marginal, assuming the source and destination
  counts are bounded by the finite total `N`. Then use a finite-protected error
  schedule for the finitely many small totals, the count-divergence theorem to
  supply the floor, count-total bounds from feasibility, and the
  FOC-to-sublinear bridge to obtain the paper's sequence-limit theorem.
- For the `0 < α < 1` top-one product estimate, factor the survival-product
  ratio over the interval between destination and source counts. Bound
  `∏(1-q_i)` by `exp(-∑ q_i)`, lower-bound the interval sum by gap length
  times the right-end success probability, and use a log-likelihood-ratio
  inequality to turn the scalar exponential bound into marginal dominance.
  Use the concrete schedule `ε_N = (N+1)^((α-1)/2)`: it tends to zero, while
  `(ε_N N - 1) q_N → ∞` for `0 < α < 1`, so it eventually dominates all finite
  log-likelihood ratios and closes the subunit branch under the explicit
  probability-validity assumptions.
- For the `α = 1` top-one product estimate, do not rely on the paper's displayed
  finite telescope unless `c` has actually been specialized to an integer. For
  real `c`, prove the finite harmonic-log route instead: show
  `log((x+1)/x) ≤ 1/x`, telescope the interval log sum, derive the
  survival-product ratio bound `P_r/P_q ≤ ((q+1+d)/(r+1+d))^c`, and then combine
  it with the source/destination success ratio and weights `p_t^(1/(1+c))`.
  The large scaled-gap-to-shifted-scalar bridge closes the raw-ordered case
  once the error schedule dominates the fixed shift
  `(1+d) * ∑_t 1 / p_t^(1/(1+c))`. Nonuniform target weights can still make a
  large scaled-count gap occur with the opposite raw order; use the reverse
  product layer there. The reverse layer bounds the inverse interval product by
  the same endpoint ratio times an explicit log-correction sum from
  `-log(1-c/x) - c log((x+1)/x)`, and an exponential scalar bridge turns the
  corrected shifted-count inequality into marginal dominance. Bound each
  correction term by `c * (1 + 2 * c) / x^2`, sum over an interval by its length
  times the left-endpoint inverse-square term, and feed the resulting
  nonnegative correction through the shift
  `1 + d + B * (exp(E / (1 + c)) - 1)`. The PRPKG alpha-one seam separates
  raw-order shift growth from reverse-order corrected-shift growth, and the
  concrete quarter-error certificate closes the branch: use
  `ε_N = (N+1)^(-1/4)` so both `ε_N N → ∞` and `ε_N^3 N → ∞`; the cube growth
  dominates the correction-sum bound after scaling by the finite target-weight
  sum.
- For the `α > 1` top-one product estimate, use target weights
  `w_t = p_t^(1/α)` and keep the proof in the same raw/reverse split as the
  `α = 1` branch. The raw-order bridge only needs the shifted-count term to be
  dominated by `ε_N N`. In the reverse-order bridge, bound the interval success
  sum by its left endpoint:
  `2 * ∑_{i=qsrc-1}^{qdst-1} q_i ≤
  (2*c*∑_t w_t^(-α)) * N * (ε_N N)^(-α)`, feed this through
  `exp(E/α)-1 ≤ exp(1)*(E/α)` once the scaled argument is below one, and bound
  the correction by a constant times `N^2 * (ε_N N)^(-α)`. The concrete
  schedule `ε_N = (N+1)^(-(α-1)/(2*(α+1)))` closes the branch because
  `ε_N → 0`, `ε_N N → ∞`, `N*(ε_N N)^(-α) → 0`, and
  `N^2*(ε_N N)^(-(α+1)) → 0`. These two limit lemmas are generic continuous
  asymptotic tools and should be reused for similar superunit inverse-power
  correction arguments before inventing a new schedule.
- Generic ranked-Bernoulli value and marginal lemmas are reusable across
  recommender papers, but keep them local while only one paper uses them or
  while the exact import topology is still changing. Move them into the shared
  recommender/probability library once a second paper needs them or the proof
  shape has stabilized.
- For finite fixed-total count-allocation optimization, encode allocations as
  functions into `Fin (N + 1)` plus a total-sum proof, optimize over that finite
  code space, then decode to the paper allocation type.
- For all-consumed linear recommendation objectives, prove both directions when
  the paper says recommendations contain only the argmax type: first show an
  all-on-argmax allocation is optimal by comparing per-item scores, then use
  the one-step FOC to show any type with strictly lower per-item score must have
  zero count in every optimum. The second direction needs strict score
  inequality and positive common mean; weak argmax assumptions only prove an
  optimal witness, not uniqueness of support.

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
- For finite symmetric recommendation LPs, avoid proving a generic "selected
  BFS" theorem if the paper result can be closed by a canonical closed-form
  construction. Prove the canonical first-crossing or first-closed pivot exists,
  prove its denominator/nonnegativity bounds, and use that pivot to build the
  closed policy/certificate. Keep selected-BFS statements as auxiliary
  explicit-input variants unless the source theorem genuinely needs arbitrary
  selected optima.
- When the recommendation model has mirror symmetry, prove the first half
  directly and derive the second half by a mirror-equivalence theorem preserving
  the objective, constraints, and optimal values.
- If a displayed paper formula depends on an implicit modeling convention, such
  as a center item counted once in a half-LP but twice in a full mirrored
  policy, split the theorem names by convention and prove an explicit bridge or
  explanation. Do not hide convention differences inside the executable model.
- For user-item fairness paper examples, do not leave source examples as bare
  definitions if they appear in the DAG. Formalize the small checked claims
  that make the example auditable, or mark the example honestly as not
  formalized. For finite two-item smoke examples over `Real`, avoid
  `native_decide`; use `finiteMin_eq_of_forall`, `Finset.sup'_le`,
  `EconCSLib.le_finiteMax`, `EconCSLib.Policy.agentScore_pure`, and, for raw
  item probabilities under deterministic policies, unfold `EconCSLib.Policy.pure`
  and simplify with `PMF.pure_apply`.
- In opposing-type LP/pivot proofs, large contexts can make a final solver call
  more expensive than the math. Before using `linarith` at the end of a long
  branch, name the scalar bounds you need (for example `ell ≤ q`, `q' ≤ ell'`,
  then `q' ≤ q`) and close by contradiction against the strict monotonicity
  fact. This is usually faster and gives better failure locations.
- If a canonical closed-form/certificate construction now discharges a previous
  selected-BFS or denominator assumption, immediately update README/DAG wording
  from `conditional` or `formalized with caveat` to `formalized`. Keep auxiliary
  explicit-input selected-BFS lemmas, but do not let their older status text
  make the final source wrapper look conditional.

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
