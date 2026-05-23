# Final Validation Report: Test-optional Policies

## Verdict

The paper-facing formalization is complete for the source models used in the
paper.

All named definitions and named results in Sections 2--4 have compiling Lean
endpoints in the compact human-review interface. The formalization did not find
a counterexample to a named theorem in the paper. It did identify two places
where the informal source proof needs to be represented carefully:

- continuous cutoff and tie cases should be stated as source-law or a.e.
  equilibrium facts, since boundary types have measure zero;
- arbitrary raw-policy abstractions are broader than the paper's source model
  and can be false, so they are recorded only as diagnostics.

Those are modeling repairs to the formal statement surface, not caveats on the
paper-facing theorem claims.

Human review is still external: the dashboard currently reports `0/16`
reviewed interface items, with no stale or mismatch entries.

## Source Surface

Human reviewers should start from:

- `PaperInterface.lean`: compact 16-row statement surface.
- `SOURCE_AUDIT.md`: source-order map from the paper text to each interface
  row, including `source.txt` line numbers and audit endpoints.
- `PostPaperAudit.lean`: broader importable ledger for proof-route variants
  and diagnostics.

The compact interface covers exactly these paper-facing items:

| Paper item | Interface coverage |
| --- | --- |
| Definition 1, equilibrium | source action, feasibility, best response, and consistency |
| Definition 2, latent-skill fairness | equality of estimate laws conditional on latent skill and observed features |
| Definition 3, observable fairness | equality of estimate laws conditional on observed features |
| Definition 4, demographic fairness | equality of estimate laws by access status |
| Definition 5, test blankness | test score has no estimate relevance |
| Theorem 3.1 | optional-reporting and report-required strategic-withholding branches |
| Theorem 3.2 | optional-reporting and report-required fairness-impossibility/no-relevance branches |
| Lemma 4.1 | observed access makes the Bayesian access-side policy strategy-proof |
| Proposition 4.2 | Bayesian optimal access-side estimates are not latent-skill fair |
| Proposition 4.3 | full Bayesian optimal policy is not observable or demographic fair |
| Definition 6 | resampling policy |
| Theorem 4.4 | resampling policy is strategy-proof, observable fair, and demographic fair |

The report intentionally does not list every helper declaration. Those details
belong in `PostPaperAudit.lean`.

## What Happened

The Section 3 proof was the hard part. The final route follows the paper's
strategic-withholding and unraveling arguments, but makes the implicit cases
explicit:

- In Theorem 3.1, optional reporting and report-required policies are handled
  separately, matching the paper's two bullet points. The formalization uses
  source-shaped Gaussian and affine payoff models to prove the threshold and
  unfairness conclusions.
- In Theorem 3.2, fairness implies either a positive reporter/taker event share
  that unravels by a profitable deviation, or a zero-event branch where the
  policy is already test-blank/no-test-relevant. This is the formal version of
  the paper's unraveling proof.
- For continuous threshold models, pointwise equilibrium at the exact cutoff is
  too strong. The repaired route uses a.e. equilibrium under the realized source
  law, which matches the paper's intended treatment of measure-zero tie points.

The observed-access section is more direct:

- Lemma 4.1 closes the strategy-proofness step for the observed-access source
  model.
- Propositions 4.2 and 4.3 close the informational-gap unfairness results using
  the shared Gaussian posterior infrastructure.
- Definition 6 and Theorem 4.4 close via a finite conditional-resampling
  kernel: access and no-access estimate laws are pushforwards of the same
  conditional test-score law, so observable fairness holds by construction and
  demographic fairness follows by mixing.

## Issues Found

No named theorem in the paper is marked false.

The main source-model issue was overgeneralization. A raw abstraction that lets
an arbitrary external Bayesian policy be paired with arbitrary pointwise
cutoff behavior is false. The paper does not need that abstraction. The valid
formal route keeps the policy tied to the source model and uses a.e. statements
for continuous boundary cases.

This distinction is important for future agents: keep diagnostics about false
overbroad abstractions out of the paper-facing theorem inventory unless they
change a named paper theorem. Here, they do not.

## Library Pass

The post-verification proof scan produced one small library extraction:

- `measure_pos_of_subset`
- `ae_property_contradicts_positive_failure_mass`

Both now live in `EconCSLib.Foundations.Probability.MeasureInequalities`, and
LG21 keeps only thin paper-local wrappers around them.

Other reusable infrastructure was already in the shared library and was reused
rather than duplicated:

- a.e. choice equilibrium:
  `EconCSLib.Foundations.Optimization.ChoiceEquilibriumAE`;
- finite event shares, binary mixtures, and blank-on-zero normalization:
  `EconCSLib.Foundations.Probability.FiniteMixture`;
- conditional resampling kernels:
  `EconCSLib.Foundations.Probability.Admissions`;
- Gaussian posterior and tail facts:
  `EconCSLib.Foundations.Probability.Gaussian`, `GaussianMathlib`, and
  `GaussianDerivatives`.

Deferred candidate: the paper-local tagged point/Gaussian/finite-mixture law
wrappers may deserve a generic Gaussian-mixture law module if another
standardized-testing paper needs the same constructors. They remain local for
now because their current shape is tuned to LG21's source-law bookkeeping.

## DAG Audit

`DependencyDAG.tex` is source-facing and follows the shared template styles:

- model/definition layers use `dag_model`;
- supporting lemma/library nodes use `dag_lemma`;
- paper-facing theorems, propositions, and final results use `dag_result`.

The final spacing pass widened the lanes, increased vertical separation, and
routed the model-to-fairness dependency vertically so arrows do not cross node
labels. `latexmk -pdf DependencyDAG.tex` rebuilt the PDF, and PNG inspection
found no node-label or arrow-through-text overlap.

## Verification Checks

Passed:

- `lake build LG21TestOptionalPolicies`
- placeholder scan for `sorry`, `admit`, `axiom`, and `unsafe` in LG21 Lean
  files
- `git diff --check` on the touched LG21/status/skill/library files
- `latexmk -pdf DependencyDAG.tex`
- dashboard cache refresh for `LG21TestOptionalPolicies`

Expected non-passing human-review check:

- `review-dashboard.sh --check` reports `0/16 reviewed`, `16 unreviewed`, `0`
  stale, and `0` mismatch. This is expected until a human completes dashboard
  review.

Repository audit:

- `python3 scripts/audit_repository.py --include-active` reports no
  elsewhere in the repository.

## Lean Footprint

- Paper-local Lean files: 127,936 total lines across nine modules.
- `PaperInterface.lean`: 92 lines.
- Human-review surface: 16 declarations.
- `PostPaperAudit.lean`: 1,073 importable audit declarations.
