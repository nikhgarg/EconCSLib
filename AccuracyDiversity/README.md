# Reconciling the Accuracy-Diversity Trade-off in Recommendations

## Source Version

- Paper: *Reconciling the accuracy-diversity trade-off in recommendations*
- Authors: Kenny Peng, Manish Raghavan, Emma Pierson, Jon Kleinberg, and Nikhil Garg
- Version formalized: TheWebConf 2024 / arXiv:2307.15142
- Official URL: https://openreview.net/forum?id=rSHR9YKBVy
- arXiv URL: https://arxiv.org/abs/2307.15142
- PDF URL: https://arxiv.org/pdf/2307.15142
- Accessed: 2026-04-23

The PDF is not committed to git. Use the OpenReview page and arXiv PDF above as
the source versions for theorem-number and definition comparisons.

## Central Theorem File

- `AccuracyDiversity/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Detailed count-allocation,
representation, Bernoulli, and exchange lemmas live in the other files in
this folder.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Count allocation and consumption-constrained objective | `ConsumptionModel.objective` | formalized | `AccuracyDiversity/Basic.lean` | none |
| Representation and γ-homogeneity profiles | `GammaHomogeneityProfile.Approx` | formalized | `AccuracyDiversity/Representation.lean` | none |
| Top-k oracle interface | `TopKValueOracle.toConsumptionModel_has_diminishing_returns` | conditional | `AccuracyDiversity/TopKOracle.lean` | oracle marginal assumptions |
| Bernoulli diminishing-return specialization | `BernoulliSatisfactionModel.toConsumptionModel_has_diminishing_returns` | formalized | `AccuracyDiversity/Bernoulli.lean` | valid Bernoulli probabilities |
| Finite fixed-total optimizer existence | `ConsumptionModel.paper_finite_optimum_exists` | formalized | `AccuracyDiversity/MainTheorems.lean` | nonempty type space |
| Bernoulli fixed-total optimizer existence | `BernoulliSatisfactionModel.paper_bernoulli_finite_optimum_exists` | formalized | `AccuracyDiversity/MainTheorems.lean` | nonempty type space |
| Finite exchange-improvement theorem | `ConsumptionModel.paper_finite_exchange_improvement` | formalized | `AccuracyDiversity/MainTheorems.lean` | none |
| Finite first-order condition at an optimum | `ConsumptionModel.paper_finite_optimum_first_order_condition` | formalized | `AccuracyDiversity/MainTheorems.lean` | finite optimality and valid one-count move |
| Bernoulli first-order condition | `BernoulliSatisfactionModel.paper_bernoulli_optimum_first_order_condition` | formalized | `AccuracyDiversity/MainTheorems.lean` | finite optimality and valid one-count move |
| Finite i.i.d. Bernoulli pairwise balance | `BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_pairwise_balanced` | formalized | `AccuracyDiversity/MainTheorems.lean` | identical likelihoods and Bernoulli success probabilities, all in `(0,1)` |
| Finite i.i.d. Bernoulli `0`-homogeneity | `BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_uniform_homogeneity` | formalized | `AccuracyDiversity/MainTheorems.lean` | positive slate size, nonempty finite type space, identical likelihoods and Bernoulli success probabilities, all in `(0,1)` |
| Uniform `[0,1]`, `k = 1` marginal algebra | `UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum`, `paper_uniform_top_one_optimum_first_order_condition` | formalized | `AccuracyDiversity/Uniform.lean`, `AccuracyDiversity/MainTheorems.lean` | none |
| Proposition 2 square-root representation bridge | `paper_uniform_sqrt_homogeneity_of_count_closeness` | formalized | `AccuracyDiversity/MainTheorems.lean` | none |
| Proposition 2 (Uniform Homogeneity) | `paper_proposition_2` | formalized | `AccuracyDiversity/MainTheorems.lean` | none |
| Theorem 1 (Bernoulli Homogeneity) | `paper_theorem_1_bernoulli_asymptotic_homogeneity` | formalized interface | `AccuracyDiversity/MainTheorems.lean` | asymptotic limit machinery (`TendsToZero` bounds) |
| Theorem 2 (Tail Behavior) | `paper_theorem_2_tail_dependent_homogeneity` | formalized interface | `AccuracyDiversity/MainTheorems.lean` | tail-index mapping, limit machinery |
| Proposition 3 (Mixed Types) | `paper_proposition_3_mixed_homogeneity` | formalized interface | `AccuracyDiversity/MainTheorems.lean` | mixed-type limit dominance |

## Formalization Achievements

1.  **Analytic Real-Relaxation Core:**
    - Defined unshifted (`uniformSqrtTarget`) and shifted (`uniformSqrtShiftedTarget`) targets in `AccuracyDiversity/Uniform.lean`.
    - Identified the scaling identity `likelihood t = scale * shift t ^ 2`, isolating the continuous FOC exactly.
2.  **Discrete-Analytic Bridges:**
    - Established the structural theorems showing optimal counts for uniform $k=1$ bracket a shifted square-root target with strict anchor proximity without crossing.
    - Designed the rounding combinatorics needed to strictly bound representation error by $(2T+2)/N$ explicitly via no-crossing lemmas in `Math/FiniteRounding.lean`.
    - Completely verified **Proposition 2** for finite rounding accuracy without `sorry`.
3.  **Tail Index and Homogeneity:**
    - Defined `HasTailIndex` and `HasTypeTailIndex` in `AccuracyDiversity/Pareto.lean` to formalize power-law marginal decay.
    - Verified the pairwise constraint bounds scaling for Pareto conditionally and the strict cross-type boundary conditions for mixed types (Bernoulli-Uniform).
4.  **Asymptotic Framework:**
    - Established topological scaffold interfaces for sequences in `EconCSLean/Math/Asymptotics.lean`.
    - Integrated limits into the public theorem interface in `MainTheorems.lean`.

## Future Work (The Seams)

- **Asymptotic Limit Machinery:** The transitions from finite-count bounds (e.g., $(q_i - q_j) \le C$ or $\log$ boundaries) to representation topological limits ($q_i/N \to 1/T$) are defined as `sorry`ed interfaces in the `Asymptotics` sub-library and limits.
- **Order Statistics:** The `TopKValueOracle` remains abstract for arbitrary distributions.
