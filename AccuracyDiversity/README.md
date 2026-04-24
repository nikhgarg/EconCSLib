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
representation, Bernoulli, top-k, and exchange lemmas live in the other files in
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
| Uniform `[0,1]`, `k = 1` marginal algebra | `UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum`, `paper_uniform_top_one_optimum_first_order_condition` | formalized | `AccuracyDiversity/Uniform.lean`, `AccuracyDiversity/MainTheorems.lean` | finite optimality and valid one-count move |
| Proposition 2 square-root representation bridge | `paper_uniform_sqrt_homogeneity_of_count_closeness` | formalized bridge | `AccuracyDiversity/MainTheorems.lean` | requires a count-closeness theorem for the square-root target |
| Appendix D.5 rounding combinatorics and exchange certificate bridge | `paper_rounding_count_close_of_no_crossing`, `paper_uniform_rounding_count_close_of_strict_exchange_certificate`, `paper_uniform_rounding_count_close_of_two_anchor_certificate`, `paper_uniform_rounding_count_close_of_shifted_square_anchors` | formalized bridge | `AccuracyDiversity/MainTheorems.lean` | requires constructing lower/upper anchors that bracket the squared shifted real targets |
| Finite Proposition 2 anchor-certificate theorem | `paper_uniform_top_one_sqrt_homogeneity_of_anchor_certificate`, `paper_uniform_top_one_sqrt_homogeneity_of_two_anchor_certificate`, `paper_uniform_top_one_sqrt_homogeneity_of_shifted_square_anchors` | formalized bridge | `AccuracyDiversity/MainTheorems.lean` | requires constructing the square-root lower/upper anchors and proving one-item closeness to the square-root target |
| Two-type Bernoulli exchange inequalities | `paper_two_type_forward_one_le_backward_zero`, `paper_two_type_forward_zero_le_backward_one` | formalized | `AccuracyDiversity/MainTheorems.lean` | finite optimality and positive source count |
| Two-type symmetric Bernoulli balance and equal-representation homogeneity | `paper_symmetric_two_type_bernoulli_optimum_balanced`, `paper_symmetric_two_type_bernoulli_optimum_equal_homogeneity` | formalized | `AccuracyDiversity/MainTheorems.lean` | symmetric likelihood/probability assumptions and positive slate size for homogeneity |
| Asymptotic homogeneity of optima | `ConsumptionModel.AsymptoticHomogeneityTarget` | scaffold | `AccuracyDiversity/Optimization.lean` | connect finite exchange inequalities to asymptotic approximation bounds |

The finite i.i.d. Bernoulli result is the closed finite-count core of the
paper's Bernoulli `0`-homogeneity claim. The broader Theorem 1/2/3 statements
still need order-statistic and asymptotic-limit machinery for general bounded,
exponential, Pareto, and non-identical Bernoulli item-value models.
For Proposition 2, the uniform `k = 1` marginal formulas, square-root
homogeneity representation bridge, and finite rounding-to-homogeneity assembly
are formalized. The combinatorial half of Appendix D.5 is also formalized, and a
strict boundary exchange certificate is proved sufficient to rule out high/low
integer crossings. The generic rounding layer now includes both single-anchor
and two-anchor versions; the two-anchor version matches floor/ceiling-style
real-relaxation arguments. The remaining mathematical work is the
real-relaxation optimizer and the proof that the square-root lower/upper
anchors bracket the shifted square-root real targets and have one-item
closeness to the square-root target.
