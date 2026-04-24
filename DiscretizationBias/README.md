# Addressing Discretization-Induced Bias in Demographic Prediction

## Source Version

- Paper: *Addressing Discretization-Induced Bias in Demographic Prediction*
- Authors: Evan Dong, Aaron Schein, Yixin Wang, and Nikhil Garg
- Version formalized: arXiv:2405.16762 / ACM FAccT 2024 version
- arXiv URL: https://arxiv.org/abs/2405.16762
- PDF URL: https://arxiv.org/pdf/2405.16762
- Official URL: https://doi.org/10.1093/pnasnexus/pgaf027
- Accessed: 2026-04-24

The PDF is not committed to git. Use the arXiv URL above as the source version
for theorem-number and definition comparisons.

## Central Theorem File

- `DiscretizationBias/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Reusable decision-rule
lemmas live in `EconCSLean/Decision/Argmax.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Theorem 2(i), finite deterministic optimizer existence | `paper_theorem2i_finite_objective_optimizer_exists` | formalized finite objective-existence core | `DiscretizationBias/MainTheorems.lean` | finite dataset/action model; paper objective supplied as a real-valued rule functional |
| Theorem 2(ii), argmax is accuracy-maximizing for Bayes-optimal scores | `paper_theorem2ii_argmax_accuracy_maximizing` | formalized finite deterministic core | `DiscretizationBias/MainTheorems.lean` | deterministic finite dataset/label model; posterior scores supplied directly |
| Theorem 1, argmax bias bounded by MAE and tight | none | not formalized | none | requires calibrated continuous predictors, MAE, bias metrics, and the paper's measure-theoretic transformation argument |
| Theorem 2(i), paper-specific fidelity/accuracy objective | none | not formalized | none | requires formal definitions of the paper's reference distribution, fidelity objective, and objective weights |
| Theorem 2(iii), uniqueness/Pareto optimality of argmax among independent rules | none | not formalized | none | requires randomized independent decision rules, non-trivial reference distributions, and Pareto-frontier definitions |
