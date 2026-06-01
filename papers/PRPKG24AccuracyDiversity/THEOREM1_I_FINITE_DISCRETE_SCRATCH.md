# Theorem 1(i) Finite-Discrete Scratch

Active Lean target:
instantiate `TopKUniformGeometricTailCertificate` for a general finite-support
top-`k` distribution.

Paper setup:
`D` has finite support `x1 > x2 > ... > xr`, top-mass `q = Pr[X = x1]`,
fixed consumed count `k`, and all type likelihoods are positive.  For a type
count `a`, `h(a)` is the expected sum of the top `k` values among `a` draws.

Distribution estimate being formalized:
there are constants `c, C > 0`, integer `d`, base `rho = 1 - q` with
`0 < rho < 1`, and a finite floor such that for all large enough `a`,

```text
c * rho^a <= h(a + 1) - h(a)
h(a) - h(a - 1) <= C * a^d * rho^a.
```

Why this should be true:
adding one draw only changes the top-`k` sum substantially when the existing
sample has fewer than `k` top-support draws.  The binomial probability
`Pr[Bin(a,q) <= k-1]` is at most a degree-`k-1` polynomial times `rho^(a-k+1)`.
For a lower bound, use the event that the new item is top-support and the old
sample has exactly `k-1` top-support draws; after a fixed floor this gives a
positive multiple of `rho^a`.  The gain is at least the top gap `x1 - x2`.

Lean endpoints now available:

- `TopKUniformGeometricTailCertificate` converts a finite-floor positive
  forward marginal and polynomial-geometric/geometric marginal tails into the
  verified uniform homogeneity theorem.
- `finiteDiscreteTopMassFailureTail_le_polynomial_geometric_at_a` proves the
  upper binomial event bound in certificate-normalized `C * a^k * rho^a` form.
- `finiteDiscreteTopMassPromotingEvent_lower_geometric_at_a` proves the lower
  exact-event bound in certificate-normalized `c * rho^a` form.
- `TopKUniformGeometricTailCertificate.of_binomial_event_bounds` consumes
  weighted marginal bounds in terms of those two events and produces the
  geometric-tail certificate.
- `TopKUniformGeometricTailCertificate.of_unweighted_binomial_event_bounds`
  handles the type-likelihood weights using explicit lower/upper likelihood
  bounds.
- `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds`
  states the current source-facing endpoint directly for the paper's common
  scalar `h(a)`.
- `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds`
  instantiates that scalar seam for `finiteDiscreteIidTopKExpected`, absorbing
  the off-by-one upper-tail normalization into
  `backwardLoss = k * x1 * rho^{-1}` and using
  `forwardGain = x1 - x2`.
- `paper_theorem1_i_finite_discrete_scalar_lower_marginal_top_event_before_k`
  proves the small-count lower marginal: if `a < k`, then a new top-support
  draw contributes at least `x1`, so
  `x1 * Pr[X = x1] <= h(a+1)-h(a)`.
- `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor`
  sets `floor = k - 1` and `smallForward = x1 * q`, so the finite floor
  certificate is no longer an assumption.
- `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay`
  derives the large-gap dominance inequality from the cleaner asymptotic
  `Tendsto (fun N => (N : ℝ)^k * rho^(gap N)) atTop (nhds 0)`.
- `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap`
  closes that asymptotic obligation with the concrete schedule
  `gap N = Nat.sqrt N`, proving both sublinearity and the
  polynomial-times-geometric decay needed by the certificate.
- `FiniteDiscreteOrderStats.lean` defines `topKSumOn` for finite samples and
  proves:
  - `paper_theorem1_i_finite_discrete_expected_topK_upper_marginal_failure_prob`,
    the expected upper marginal bound by `k * x1` times the failure event.
  - `paper_theorem1_i_finite_discrete_expected_topK_lower_marginal_promoting_event`,
    the expected lower marginal bound by `(x1 - x2)` times the exact
    `k-1`-top plus new-top promoting event.
  - `paper_theorem1_i_finite_discrete_product_failure_tail_exact` and
    `paper_theorem1_i_finite_discrete_product_promoting_event_exact`, the exact
    iid product/binomial probabilities of those events.
  - `paper_theorem1_i_finite_discrete_scalar_upper_marginal_failure_tail` and
    `paper_theorem1_i_finite_discrete_scalar_lower_marginal_promoting_event`,
    the natural scalar `h(a+1)-h(a)` bounds for
    `finiteDiscreteIidTopKExpected`.

How it feeds the verified Lean bridges:

1. Count floor:
   `TopKUniformCountFloorCertificate` follows because the source backward
   marginal tends to zero with `a`, while every destination count up to a fixed
   floor has a positive forward marginal.
2. Large-gap dominance:
   after the count floor, if `qsrc - qdst` grows faster than `log N` and
   `qsrc <= N`, the ratio of the source upper bound to the destination lower
   bound is at most a constant times `N^d * rho^(qsrc-qdst)`, which tends to
   zero.
3. Homogeneity:
   the already-verified
   `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_eventual_topk_foc_certificate`
   converts these two estimates into the source `0`-homogeneity conclusion.

Current scalar bounds:

```text
top_gap * finiteDiscreteTopMassPromotingEvent k a q rho
  <= h(a + 1) - h(a)
h(a) - h(a - 1)
  <= max_loss * finiteDiscreteTopMassFailureTail k a q rho
```

The deterministic top-`k` part, product-PMF/binomial layer, and `Fin a` to
`Option (Fin a)` marginal identity are now done for `h(a+1)-h(a)`. The upper
backward marginal in the scalar homogeneity seam is `h(a)-h(a-1)`, and the
new iid scalar assembly theorem now uses
`paper_theorem1_i_finite_discrete_top_mass_failure_tail_pred_le_inv_mul` to
move the verified `a-1` failure tail to the certificate's size-`a` tail and
absorb the fixed `rho^{-1}` factor into `backwardLoss`.

Those two inequalities are now exactly the hypotheses of
`paper_theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds`.
The `k - 1` pred-floor wrapper now also proves:

```text
smallForward <= h(a+1)-h(a)     for all a <= floor
```

with `smallForward = x1 * q`. The finite-discrete top-support source branch is
now closed under the explicit assumptions in the paper-facing sqrt-gap wrapper:

```text
gap(N)/N -> 0
N^k * rho^(gap N) -> 0 strongly enough for the certificate inequality
```

from primitive assumptions. The constant-heavy certificate inequality itself is
proved by the gap-decay wrapper, and the displayed source-shaped asymptotics
are supplied by the sqrt-gap wrapper. The next PRPKG Theorem 1 targets are the
bounded, exponential, and Pareto distribution certificates, followed by the
Corollary 1 construction.
