# PRPKG24 Handoff: 2026-05-22 Stopping Point

Superseded for current pickup by
`HANDOFF_2026-05-23_PRPKG_STOPPING_POINT.md`. Keep this file as historical
context for the bounded/Pareto source-assumption boundary reached on
2026-05-22.

## Start Here

This handoff supersedes the older May 17 pickup note for the current PRPKG
thread. The older note remains useful for the long declaration inventory, but
the state below is the current stopping point.

Shared worktree warning: other agents have concurrent edits in EOS, GLM, GN,
LG, MBJG, and skill files. Stage only PRPKG-owned paths and the one status doc.
Do not stage the pre-existing untracked `PaperInterface.lean` or the
`review_slices.json` deletion unless you intentionally regenerate/review them.

## Verified Boundary

Last local validation:

```bash
lake build PRPKG24AccuracyDiversity
```

It passed after the bounded Lemma D.2 source-assumption work, exact
bounded/Pareto scaled-marginal certificates, Corollary 1 bounded/Pareto power
realizations, Definition 3/Proposition 5 order-statistic interface, and the
conditional Proposition 4 endpoint.

There are no PRPKG-local `sorry`/`admit` proof holes in the Lean files.

## What Changed In This Thread

- `Bounded.lean`: closed the direct bounded Lemma D.2 local-CDF-power route.
  The new route derives local power bounds from
  `BoundedTailCDFPowerSandwich`, proves the growing near-zero dominated
  convergence bridge, constructs finite/asymptotic split certificates from
  monotone bounded-support assumptions, and exposes the exact bounded
  power-marginal scaled-marginal certificate.
- `Pareto.lean`: added the exact Pareto power-marginal scale and reusable
  scaled-marginal limit certificate.
- `MainTheorems.lean` and `ProofInterface.lean`: exposed paper-facing wrappers
  for Lemma D.2, Lemma 1, bounded/Pareto scaled-marginal checkpoints,
  Corollary 1 bounded/Pareto concrete power-marginal realizations,
  Definition 3/Proposition 5 order-statistic-mean interfaces, and the
  conditional Proposition 4 continuous-sphere minimization endpoint.
- `TopKOracle.lean`: added
  `orderStatisticTopKSumFromMean` and
  `TopKValueOracle.ofOrderStatisticMean`, matching the paper's bottom-indexed
  `mu_D(i,a)` convention.
- `Uniform.lean`: connected the bottom-indexed uniform order-statistic means
  `i/(a+1)` to the existing top-indexed uniform closed form.
- `README.md`, `FORMALIZATION_PLAN.md`, and
  `docs/ECONCSLEAN_CURRENT_STATUS.md`: updated the audit/status to reflect the
  current source-assumption boundaries rather than stale `sorry` or
  unformalized labels.

## Current Paper Status

Closed or effectively closed:

- Example 1 exact all-consumed side and displayed log-relaxation calculation.
- Definitions 1 and 2 at the paper-formula level.
- Definition 3 / Proposition 5 as a source-assumption interface, with the
  uniform `[0,1]` instance bridged to the existing closed form.
- Theorem 1(i) finite-discrete scaffolding and a fully formalized Bernoulli
  top-one instance.
- Theorem 1(ii) uniform `beta = 1` checkpoint and exact bounded
  power-marginal optimization/scaled-marginal checkpoint.
- Theorem 1(iii) exponential finite-sample top-`k` order-statistic route.
- Theorem 1(iv) exact Pareto power-marginal optimization/scaled-marginal
  checkpoint.
- Theorem 1(v) common-mean all-consumed/no-consumption-constraint core.
- Lemma 1 and Lemma D.2 from explicit bounded-tail CDF/source integral
  assumptions.
- Proposition 4 final minimization step from an explicit continuous-sphere
  analytic certificate.

Main remaining source work:

- General bounded-support order-statistic derivation: instantiate actual
  `mu_D(i,a)`/top-`k` means from a sampled bounded-support distribution and
  connect them to the reflected-CDF integral interface used by Lemma D.2 and
  Lemma 1.
- Pareto order-statistic derivation: prove the source distribution really
  yields the power marginal law, or an asymptotically equivalent
  scaled-marginal source certificate.
- Corollary 1 full distribution construction: the bounded/Pareto
  optimization-oracle realizations are now concrete, but the final statement
  still needs source-distribution instantiations for all cases.
- Proposition 2/Lemma D.5: the uniform route is strong and audited, but the
  paper's sharp finite rounding route remains caveated because the printed
  relaxed optimizer has a documented total-mass issue.
- Proposition 4 analytic sphere layer: profile space, uniform sphere measure,
  cosine-distance kernel, full-support user measure, Fubini/symmetry constant,
  and Laplace-principle reduction.

## Suggested Next Step

Resume with the bounded-support source distribution layer. The most valuable
target is a theorem that takes a concrete sampled bounded-support law and
proves that its order-statistic top-`k` mean equals the reflected-CDF integral
interface already consumed by Lemma 1 / Lemma D.2. This is the shortest path
from the current certificate boundary to the full Theorem 1(ii) distribution
claim.

After that, move to the Pareto source-order-statistic derivation. The optimizer
and scaled-marginal seams are already closed, so the remaining Pareto work
should be kept focused on the distribution-to-marginal bridge.
