# PRPKG24 Pickup Note

Read `HANDOFF_2026-05-23_PRPKG_STOPPING_POINT.md` first. The older
`HANDOFF_2026-05-22_PRPKG_STOPPING_POINT.md` and
`HANDOFF_2026-05-17_WEEK_PAUSE.md` files are historical records for earlier
bounded-source checkpoints.

## Current Boundary

- Validation baseline: `lake build PRPKG24AccuracyDiversity` passed at the
  2026-05-23 stopping point.
- Shared worktree: many unrelated files are dirty. Stage only PRPKG-owned paths
  and the exact reusable library/skill files you edit.
- Strongest new endpoint: Pareto Lemma D.4's exact gamma-ratio source sequence
  is formalized through
  `paper_lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit`.
- Reusable transfer: `EconCSLib.Foundations.Math.GammaAsymptotics` now contains
  the generic Gamma-ratio asymptotic and finite-difference bridge.

## Next Work

1. Pareto: identify the actual Pareto order-statistic mean `mu_D(q-r,q)` with
   `paretoRankGammaRatioMean alpha r q`, or prove an equivalent source
   sequence, then feed fixed ranks into
   `paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_pareto_rank_scaled_limits`.
2. Bounded: instantiate `BoundedTailCDFPowerSandwich` for
   `reflectedCDFMass baseMeasure M`, then use the reflected-CDF Lemma 1
   endpoints and the `_and_scaled_drop` bounded marginal wrappers.
3. Corollary 1: assemble the distribution witnesses after the bounded and
   Pareto source-distribution certificates exist.

## Do Not Redo

- Proposition 2 / uniform optimizer algebra.
- Theorem 1(i) finite-discrete and Bernoulli top-one source bounds.
- Theorem 1(iii) exponential finite-sample top-`k` order-statistic route.
- Bounded Lemma D.2 finite-sum/reflected-CDF analytic assembly.
- Pareto gamma-ratio algebra in `GammaAsymptotics` and `Pareto.lean`.

## First Commands

```bash
lake build PRPKG24AccuracyDiversity
rg -n "\b(sorry|admit)\b" papers/PRPKG24AccuracyDiversity EconCSLib/Foundations/Math/GammaAsymptotics.lean
rg -n "paretoRankGammaRatioMean|paper_lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit|scaled_difference_limit_of_value_asymptotic_and_scaled_drop" papers/PRPKG24AccuracyDiversity EconCSLib/Foundations/Math/GammaAsymptotics.lean
```
