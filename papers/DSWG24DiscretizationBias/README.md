# Addressing Discretization-Induced Bias in Demographic Prediction

## Source Version

- Paper: *Addressing Discretization-Induced Bias in Demographic Prediction*
- Authors: Evan Dong, Aaron Schein, Yixin Wang, and Nikhil Garg
- Version checked locally: cached arXiv PDF created 2024-05-27; README source label says arXiv:2405.16762 / ACM FAccT 2024 version
- arXiv URL: https://arxiv.org/abs/2405.16762
- PDF URL: https://arxiv.org/pdf/2405.16762
- Official URL: https://doi.org/10.1093/pnasnexus/pgaf027
- Accessed: 2026-04-24

The PDF is cached locally as `DSWG24DiscretizationBias.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache
`DSWG24DiscretizationBias.txt` is used for named-statement searches; refresh it
only if the source PDF changes. Use this local PDF for theorem-number and
definition comparisons before refreshing from arXiv.

## Central Theorem File

- `DSWG24DiscretizationBias/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Reusable decision-rule
lemmas live in `EconCSLib/Foundations/Optimization/Argmax.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Theorem 1, argmax bias bounded by MAE and tight | none | not formalized | none | requires calibrated continuous predictors, MAE, bias metrics, and the paper's measure-theoretic transformation argument |
| Theorem 2(i), joint rule maximizes `O_N^γ` | `paper_theorem2i_joint_optimization_rule_exists`, `paperExpectedONObjective`, `paperONObjective` | conditional | `DSWG24DiscretizationBias/MainTheorems.lean`, `EconCSLib/Foundations/Optimization/Argmax.lean` | Previous status: conditional source-facing statement; assumes `FiniteLinearExpectation` for the outer dataset expectation and row-wise Bayes identities `hbayesRow`; fidelity/reference distribution is supplied as the paper's per-dataset fidelity term |
| Theorem 2(ii), argmax is accuracy-maximizing for Bayes-optimal scores | `paper_theorem2ii_argmax_expected_accuracy_maximizing` | conditional | `DSWG24DiscretizationBias/MainTheorems.lean`, `EconCSLib/Foundations/Optimization/Argmax.lean` | Previous status: conditional source-facing statement; assumes `FiniteLinearExpectation` and row-wise Bayes identities `hbayesRow`; `expectedDecisionAccuracy_eq_expectedDecisionScore_of_row_bayes` proves these imply the full tower-property bridge for every joint rule |
| Theorem 2(ii), deterministic Bayes-score core | `paper_theorem2ii_argmax_accuracy_maximizing` | partially formalized | `DSWG24DiscretizationBias/MainTheorems.lean` | Previous status: auxiliary lemma; fixed observed dataset; retained only as a local support wrapper |
| Theorem 2(iii), uniqueness/Pareto optimality of argmax among independent rules | none | not formalized | none | requires randomized independent decision rules, non-trivial reference distributions, and Pareto-frontier definitions |

## Source-Audit Notes

The cached PDF has two named theorems. The DAG has been checked against those
named source statements:

- Theorem 1 is fully open: argmax bias under calibrated continuous classifiers,
  upper bound by MAE, and tightness.
- Theorem 2(i)-(ii) now use the actual paper objective with expected true
  accuracy plus expected fidelity. The reusable bridge proves that row-wise
  Bayes identities imply the full tower-property equality for every joint rule.
  A concrete measure/disintegration model proving those row identities from
  `q(y,x)=Pr(Y=y|X=x)` remains open.
- Theorem 2(iii) remains open and should not be marked as covered by the
  optimizer/argmax wrappers.
