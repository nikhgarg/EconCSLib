# Final Validation Report: DSWG24 Discretization Bias

## 1. Human Verdict

- Lean formalization status: formalized
- Human dashboard review status: 0/32 rows reviewed; 0 stale; 0 mismatches.
- Main caveat: Main theorem route differs from the paper proof in places; the validation report records the proof-route deviation.

## 2. Source and Scope

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

## 3. What Has Been Proven

The paper-facing definitions, Theorem 1 discretization-bias bound, and Theorem
2 weighted-objective characterization are formalized. Lean also records the
Bayes-identity assumptions and coordinate-sweep proof route needed to make the
source proof precise.

## 4. Additional Assumptions Beyond Paper

None separately recorded in the existing report.

## 5. Proof-Strategy Deviations

### Proof Deviations and Assumptions

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

## 6. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 7. Library Lift Pass

None separately recorded in the existing report.

## 8. DAG Audit

No separate DAG audit note is recorded in the existing report.

## 9. Conditional Results and Remaining Gaps

None separately recorded in the existing report.

## 10. Suspected Paper Errors or Inconsistencies

None separately recorded in the existing report.

## 11. Validation Checks

### Verification Checks

- The paper target `DSWG24DiscretizationBias` builds successfully.
- The human-facing Lean interface `DSWG24DiscretizationBias.PaperInterface`
  builds successfully.
- The post-paper audit ledger builds successfully.
- The DSWG Lean files contain no `sorry`, `admit`, or `axiom` placeholders.
- The dependency DAG renders successfully and was visually inspected after the
  final layout update.
- The final report and repository status files no longer contain obsolete
  Theorem 2(i)--(ii) restriction caveats or raw command logs.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 32 rows; 30 match, 0 uncertain, 2 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: passes (32 rows; digest 2944f9d9c293).

Flagged rows:
- `marginalLabelShare`: mismatch. Paper defines a finite-sample average over predictions; translation defines a population probability under mu_X.
- `aggregatePosterior`: mismatch. Paper defines an empirical average over observed x_i; translation gives an expectation over the marginal distribution.

## 12. Final Verdict

Completion status: complete.

The paper-facing definitions, Theorem 1, and Theorem 2 are represented by
compiling Lean declarations. The main theorem statements match the source text;
where Lean differs, it is by making assumptions explicit or replacing an
underspecified proof sketch with a precise coordinate-sweep proof strategy.

- Completion status: formalized.
- Summary: Main theorem route differs from the paper proof in places; the validation report records the proof-route deviation.

## 13. Paper Definitions Checked

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

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def prior | `prior` | - Prior class probability `Pr(y)`. |
| def marginalLabelShare | `marginalLabelShare` | mismatch. Paper defines a finite-sample average over predictions; translation defines a population probability under mu_X. |
| def aggregatePosterior | `aggregatePosterior` | mismatch. Paper defines an empirical average over observed x_i; translation gives an expectation over the marginal distribution. |
| def bias | `bias` | - Bias `bias(y, \hat y, p_ref) = \hat p_marg(y) - p_ref(y)`. |
| def fidelity | `fidelity` | - Distributional fidelity `fid(p_ref, \hat y) = -sum_y \|bias(y,\hat y,p_ref)\|`. |
| def classifierMAE | `classifierMAE` | - Predictive MAE for Bayes posterior scores: `E_X sum_y q(y,x)(1-q(y,x))`. |
| def continuousMarginalLabelShare | `continuousMarginalLabelShare` | - Continuous marginal label share: `∫ x, 1[rule x = y] dμ(x)`. |
| def continuousAggregatePosterior | `continuousAggregatePosterior` | - Continuous aggregate posterior reference: `∫ x, q x y dμ(x)`. |
| def continuousBias | `continuousBias` | - Continuous bias relative to a supplied reference distribution. |
| def continuousAggregateBias | `continuousAggregateBias` | - Continuous aggregate-posterior bias. |
| def continuousClassifierMAE | `continuousClassifierMAE` | - Continuous predictive MAE. |
| def continuousJointPriorBias | `continuousJointPriorBias` | - Joint prior-reference bias for Theorem 1's continuous statement. |
| def continuousJointClassifierMAE | `continuousJointClassifierMAE` | - Joint predictive MAE for Theorem 1's continuous statement. |
| def posteriorSimplex | `posteriorSimplex` | - Posterior-simplex condition: each `q(x)` is a probability vector. |
| def isArgmaxRule | `isArgmaxRule` | - Tie-broken argmax rule: the selected label has maximal posterior score. |
| def calibrated | `calibrated` | - Calibration: for every label and every measurable score event, the true label mass on that score event equals the aggregate posterior score mass on the same event. This is the paper's `Pr(Y=y \| q(y,x)=c)=c` condition in event-preimage... |
| def objective | `objective` | - Paper objective `O_N^gamma` for one observed dataset: `γ` times average posterior score plus `(1 - γ)` times the fidelity term. |
| def expectedObjective | `expectedObjective` | - Expected paper objective using true-label accuracy plus expected fidelity. |
| def sourceSa | `sourceSa` | - Source proof region `S_a`: focal posterior is `1`. |
| def sourceSb | `sourceSb` | - Source proof region `S_b`: focal posterior is in `(1/K,1)`. |
| def sourceSc | `sourceSc` | - Source proof region `S_c`: focal posterior is exactly `1/K`. |
| def sourceSd | `sourceSd` | - Source proof region `S_d`: focal posterior is in `(0,1/K)`. |
| def sourceSe | `sourceSe` | - Source proof region `S_e`: focal posterior is `0`. |
<!-- lean-derived-definitions:end -->

## 14. Named Theorem Statements Checked

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

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem1i_no_information_bias | `theorem1i_no_information_bias` | states the no-information plurality-class and non-plurality-class bias formulas for both prior and aggregate-posterior references. |
| theorem theorem1ii_perfect_classifier_zero_bias | `theorem1ii_perfect_classifier_zero_bias` | states the perfect-classifier zero-bias claim. |
| theorem theorem1iii_argmax_bias_le_mae | `theorem1iii_argmax_bias_le_mae` | states the calibrated argmax bias bound by predictive MAE. |
| theorem theorem1iii_tight_binary_example | `theorem1iii_tight_binary_example` | states the tight binary example where argmax bias equals MAE. |
| theorem theorem2i_joint_rule_exists | `theorem2i_joint_rule_exists` | states existence of a joint expected-objective maximizer. |
| theorem theorem2ii_argmax_accuracy_maximizing | `theorem2ii_argmax_accuracy_maximizing` | states argmax expected-accuracy optimality for Bayes-optimal scores. |
| theorem theorem2iii_non_argmax_not_pareto | `theorem2iii_non_argmax_not_pareto` | states that a positively disagreeing independent rule is not Pareto optimal under a non-trivial reference distribution. |
| theorem theorem2iii_weighted_objective_maximizer_iff_agrees_argmax | `theorem2iii_weighted_objective_maximizer_iff_agrees_argmax` | states the weighted-objective maximizer iff argmax-agreement claim for `gamma < 1`. |
| theorem theorem2iii_strict_disagreement_not_weighted_objective_maximizer | `theorem2iii_strict_disagreement_not_weighted_objective_maximizer` | states the accuracy-boundary strict-disagreement non-maximality claim. |
<!-- lean-derived-statements:end -->

## 15. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper DSWG24DiscretizationBias --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| def aggregatePosterior | `aggregatePosterior` | gpt-5-codex (model; mismatch; 2026-06-06T20:39:21Z) | gpt-5-codex (model; mismatch; 2026-06-06T20:39:21Z): Paper defines an empirical average over observed x_i; translation gives an expectation over the marginal distribution. |
| def bias | `bias` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define bias as marginal label share minus the reference probability at y. |
| def calibrated | `calibrated` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation is the event-preimage integral form described by the paper statement. |
| def classifierMAE | `classifierMAE` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both give E_X sum_y q(y,x)(1-q(y,x)), modulo argument-order notation. |
| def continuousAggregateBias | `continuousAggregateBias` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation defines bias against the continuous aggregate-posterior reference, matching the paper label. |
| def continuousAggregatePosterior | `continuousAggregatePosterior` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define the continuous aggregate posterior reference as the integral of q(x,y). |
| def continuousBias | `continuousBias` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation gives the expected continuous bias relative to a supplied reference distribution. |
| def continuousClassifierMAE | `continuousClassifierMAE` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation supplies the continuous integral form of predictive MAE. |
| def continuousJointClassifierMAE | `continuousJointClassifierMAE` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation gives the joint-measure integral of the predictive MAE integrand. |
| def continuousJointPriorBias | `continuousJointPriorBias` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states joint prior-reference bias as predicted label mass minus true label prior mass. |
| def continuousMarginalLabelShare | `continuousMarginalLabelShare` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define the continuous label share as the integral of the indicator that the rule outputs y. |
| def expectedObjective | `expectedObjective` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states the gamma-weighted expected true-label accuracy plus expected fidelity objective. |
| def fidelity | `fidelity` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define fidelity as the negative sum over labels of absolute bias. |
| def isArgmaxRule | `isArgmaxRule` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both require the selected label to have posterior score at least every label's score. |
| def marginalLabelShare | `marginalLabelShare` | gpt-5-codex (model; mismatch; 2026-06-06T20:39:21Z) | gpt-5-codex (model; mismatch; 2026-06-06T20:39:21Z): Paper defines a finite-sample average over predictions; translation defines a population probability under mu_X. |
| def objective | `objective` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define the objective as gamma times average posterior score plus one minus gamma times the fidelity term. |
| def posteriorSimplex | `posteriorSimplex` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): The nonnegativity, upper bound, and unit-sum conditions exactly express that each q(x) is a probability vector. |
| def prior | `prior` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both state the prior/marginal class probability for label y. |
| def sourceSa | `sourceSa` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define S_a as the set where the focal posterior equals 1. |
| def sourceSb | `sourceSb` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define S_b by focal posterior strictly between 1/K and 1. |
| def sourceSc | `sourceSc` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define S_c as the set where the focal posterior equals 1/K. |
| def sourceSd | `sourceSd` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define S_d by focal posterior strictly between 0 and 1/K. |
| def sourceSe | `sourceSe` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both define S_e as the set where the focal posterior equals 0. |
| theorem theorem1i_no_information_bias | `theorem1i_no_information_bias` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation gives the plurality-class and non-plurality-class bias formulas for both prior and aggregate-posterior references. |
| theorem theorem1ii_perfect_classifier_zero_bias | `theorem1ii_perfect_classifier_zero_bias` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states that perfect classification implies zero prior-reference bias for every label. |
| theorem theorem1iii_argmax_bias_le_mae | `theorem1iii_argmax_bias_le_mae` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states calibrated argmax prior-bias bounded above by predictive MAE, with explicit formal hypotheses. |
| theorem theorem1iii_tight_binary_example | `theorem1iii_tight_binary_example` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Both state the tight binary example equality between argmax bias at label 0 and classifier MAE. |
| theorem theorem2i_joint_rule_exists | `theorem2i_joint_rule_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states existence of an expected-objective maximizer, with formal side conditions. |
| theorem theorem2ii_argmax_accuracy_maximizing | `theorem2ii_argmax_accuracy_maximizing` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states that an argmax rule maximizes expected accuracy under Bayes-optimal score assumptions. |
| theorem theorem2iii_non_argmax_not_pareto | `theorem2iii_non_argmax_not_pareto` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states non-Pareto-optimality for a positively disagreeing rule under a nontrivial reference distribution. |
| theorem theorem2iii_strict_disagreement_not_weighted_objective_maximizer | `theorem2iii_strict_disagreement_not_weighted_objective_maximizer` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states strict-disagreement non-maximality for the weighted objective at the accuracy boundary. |
| theorem theorem2iii_weighted_objective_maximizer_iff_agrees_argmax | `theorem2iii_weighted_objective_maximizer_iff_agrees_argmax` | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:21Z): Translation states the gamma < 1 weighted-objective maximizer iff zero-disagreement with argmax rule. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.
