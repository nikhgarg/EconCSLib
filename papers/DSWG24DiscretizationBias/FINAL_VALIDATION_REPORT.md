# Final Validation Report: DSWG24 Discretization Bias

## 1. Source and Scope

- Paper: *Addressing Discretization-Induced Bias in Demographic Prediction*
- Authors: Evan Dong, Aaron Schein, Yixin Wang, and Nikhil Garg
- Source checked: cached arXiv:2405.16762 / ACM FAccT 2024 PDF, created
  2024-05-27, with ignored local text cache used during audit
- Lean folder: `papers/DSWG24DiscretizationBias`
- Paper-facing Lean files:
  `papers/DSWG24DiscretizationBias/PaperInterface.lean`,
  `papers/DSWG24DiscretizationBias/MainTheorems.lean`, and
  `papers/DSWG24DiscretizationBias/PostPaperAudit.lean`
- DAG artifacts:
  `papers/DSWG24DiscretizationBias/DependencyDAG.tex` and rendered
  `papers/DSWG24DiscretizationBias/DependencyDAG.pdf`

Scope: this audit covers the paper's mathematical definitions and theoretical
results. The empirical sections, figures, and simulation tables are not
formalized theorem claims.

The cached source text has two named source results: Theorem 1 and Theorem 2.
No source-named Lemmas, Propositions, Corollaries, or numbered Definitions were
found.

## 2. Paper Definitions Checked

These are the mathematical objects from the paper interface. All are exposed in
`PaperInterface.lean`.

- Continuous classifier: `q(y,x)` is a posterior-probability vector over
  classes; Bayes optimal means `q*(y,x)=Pr(Y=y | X=x)`.
  Lean: `PaperInterface.posteriorSimplex`,
  `Finite.FiniteBayesDatasetModel`.
- Argmax rule: assign each row the tie-broken class `arg max_y q(y,x_i)`.
  Lean: `PaperInterface.isArgmaxRule`.
- Marginal label share:
  `p_hat_marg(y) = (1/N) sum_i 1[y_hat_i = y]`.
  Lean: `PaperInterface.marginalLabelShare`.
- Bias: `bias(y, y_hat, p_ref) = p_hat_marg(y) - p_ref(y)`.
  Lean: `PaperInterface.bias`.
- Fidelity: `fid(p_ref, y_hat) = - sum_y |bias(y, y_hat, p_ref)|`.
  Lean: `PaperInterface.fidelity`.
- Aggregate posterior: `p_agg^q(y) = (1/N) sum_i q(y,x_i)`.
  Lean: `PaperInterface.aggregatePosterior`.
- Predictive MAE: `MAE(q) = E[1 - q(Y,X)]`, represented for Bayes posterior
  scores as `E_X sum_y q(y,x)(1-q(y,x))`.
  Lean: `PaperInterface.classifierMAE`.
- Calibration: `Pr(Y=y | q(y,x)=c)=c`, used to derive
  `E_X q(y,x)=Pr(y)`.
  Lean: `PaperInterface.calibrated`.
- Expected objective:
  `O_N^gamma(D,q,p_ref) = gamma ACC_N(D,q) + (1-gamma) FID_N(D,q,p_ref)`.
  Lean: `PaperInterface.objective`.
- Non-trivial reference distribution: the reference gives enough mass to the
  argmax class in a dataset, at least `1/N`, ruling out degenerate references.
  Lean: Theorem 2(iii)'s `hnontrivial` hypotheses.
- Source proof regions: for focal class `z`, the proof partitions points into
  `S_a,S_b,S_c,S_d,S_e` according to whether `q(z,x)` is `1`, in `(1/K,1)`,
  equal to `1/K`, in `(0,1/K)`, or `0`.
  Lean: `PaperInterface.sourceSa`.

## 3. Named Theorem Statements Checked

### Theorem 1

**Paper statement.** For a calibrated classifier `q`, the argmax decision rule,
`N > K`, and reference distribution equal to either the aggregate posterior or
the prior:

1. If features give no information, so `q(y,x)=Pr(y)` for every `x,y`, argmax
   classifies all points as a plurality class and the bias is
   `1-Pr(y)` for the plurality class and `-Pr(y)` otherwise.
2. If the classifier is perfect, so `q(z,x)=1` for the true label and `0`
   otherwise, then `BIAS(y,D_argmax)=0`.
3. In general, `BIAS(y,D_argmax) <= MAE(q)`, and the bound is tight for the
   plurality class in some instance.

**Lean interface statements.**

- `PaperInterface.theorem1i_no_information_bias`: states the no-information
  plurality-class and non-plurality-class bias formulas for both prior and
  aggregate-posterior references.
- `PaperInterface.theorem1ii_perfect_classifier_zero_bias`: states the
  perfect-classifier zero-bias claim.
- `PaperInterface.theorem1iii_argmax_bias_le_mae`: states the calibrated
  argmax bias bound by predictive MAE.
- `PaperInterface.theorem1iii_tight_binary_example`: states the tight binary
  example where argmax bias equals MAE.

**Status.** Formalized. Lean makes tie-breaking, posterior-simplex, calibration,
measurability, and integrability hypotheses explicit. The theorem statement is
the same paper-facing claim; the proof route differs for the informal
continuous source-transformation argument, as described below.

### Theorem 2

**Paper statement.** For Bayes-optimal `q`, `N > K`, and all data
distributions `F`:

1. For every `gamma` and `p_ref`, there exists a joint decision rule maximizing
   `O_N^gamma(D,q,p_ref)`.
2. The argmax rule maximizes `O_N^1`, i.e. it is accuracy maximizing.
3. For non-trivial `p_ref`, argmax is the only Pareto-optimal independent rule.
   No independent rule maximizes `O_N^gamma` unless `gamma=1` and the rule
   agrees with argmax with probability 1.

**Lean interface statements.**

- `PaperInterface.theorem2i_joint_rule_exists`: states existence of a joint
  expected-objective maximizer.
- `PaperInterface.theorem2ii_argmax_accuracy_maximizing`: states argmax
  expected-accuracy optimality for Bayes-optimal scores.
- `PaperInterface.theorem2iii_non_argmax_not_pareto`: states that a positively
  disagreeing independent rule is not Pareto optimal under a non-trivial
  reference distribution.
- `PaperInterface.theorem2iii_weighted_objective_maximizer_iff_agrees_argmax`:
  states the weighted-objective maximizer iff argmax-agreement claim for
  `gamma < 1`.
- `PaperInterface.theorem2iii_strict_disagreement_not_weighted_objective_maximizer`:
  states the accuracy-boundary strict-disagreement non-maximality claim.

**Status.** Formalized. For Theorem 2(i)--(ii), Lean states Bayes optimality as
row-wise Bayes identities: expected true-label accuracy equals expected
posterior score for every row and observed-data choice rule. The finite Bayes
wrappers discharge those identities from atom-level finite PMF Bayes equations;
they are not a restriction on the theorem statement. Theorem 2(iii) is
formalized through finite, iid, augmented-atom, and Markov-kernel generated
interfaces for independent deterministic and randomized rules.

## 4. Proof Deviations and Assumptions

- **Theorem 1 proof deviation.** The paper's continuous source-transformation
  proof sketch is underspecified at the measurable transformation step and in
  the multiclass `S_b/S_d` mass accounting. Lean proves the same paper-facing
  bound directly from calibration, and formalizes the source-transformation
  route using an explicit real-coordinate sweep with coordinate pushforward and
  pullback. This is a proof-strategy deviation, not a theorem-statement change.
- **Theorem 2 Bayes assumption.** The paper phrase "Bayes optimal `q`" is
  represented by row-wise Bayes identities. A finite Bayes dataset model is
  provided as a reusable discharger for those identities.
- **Standard formal assumptions.** Lean exposes finite type, decidable equality,
  posterior-simplex, measurability, integrability, finite-measure, and
  non-trivial-reference assumptions where the paper leaves them implicit.
- **Optional future strengthening.** The accepted Theorem 1 source route uses a
  concrete coordinate sweep. A fully abstract arbitrary nonatomic transport
  theorem could later replace this proof seam. More automatic arbitrary-measure
  conditional-expectation dischargers and randomized-rule measurability wrappers
  would be reusable conveniences, not missing theorem endpoints.

## 5. Verification Checks

- The paper target `DSWG24DiscretizationBias` builds successfully.
- The human-facing Lean interface `DSWG24DiscretizationBias.PaperInterface`
  builds successfully.
- The post-paper audit ledger builds successfully.
- The DSWG Lean files contain no `sorry`, `admit`, or `axiom` placeholders.
- The dependency DAG renders successfully and was visually inspected after the
  final layout update.
- The final report and repository status files no longer contain obsolete
  Theorem 2(i)--(ii) restriction caveats or raw command logs.

## 6. Final Verdict

Completion status: complete.

The paper-facing definitions, Theorem 1, and Theorem 2 are represented by
compiling Lean declarations. The main theorem statements match the source text;
where Lean differs, it is by making assumptions explicit or replacing an
underspecified proof sketch with a precise coordinate-sweep proof strategy.
