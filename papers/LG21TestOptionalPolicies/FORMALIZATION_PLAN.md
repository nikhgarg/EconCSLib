# LG21 Formalization Plan

Last updated: 2026-05-15


## Current State

- Finite admissions decompositions are proved in `MainTheorems.lean`.
- Definition 1 now has a concrete `(Y, X)` access-action object with `Y ≥ X`
  feasibility and the optional-reporting/report-required regimes encoded.
- Definition 6 and the finite distributional core of Theorem 4.4 are proved via
  the shared conditional-resampling API.
- The shared Bayesian Gaussian estimator algebra is proved:
  `paper_bayesian_optimal_estimator_gaussian` gives the precision-weighted
  posterior mean and marginal estimate law variance formula.
- Fixed-information reporting threshold support is proved:
  `paper_reporting_gaussian_threshold_iff_cutoff` turns posterior-estimate
  threshold decisions into explicit cutoffs in one reported feature/test score.
- Theorem 3.1 now has a concrete cutoff-strategy support lemma:
  `paper_theorem3_1_reporting_threshold_of_gaussian_best_response` packages
  the Gaussian reporting decision as a finite lower-cutoff rule and proves the
  monotonicity consequence for any such cutoff rule.
- Theorem 3.2 now has PMF and continuous-law endpoints plus contrapositive
  wrappers: a concrete base/test relevance witness rules out latent-skill or
  observable fairness once the source unraveling implication is available.
- Lemma 4.1 now has its two main scalar deviation cores formalized.  For
  optional reporting, a continuous strictly increasing reported-score estimate
  plus a non-report estimate inside a nontrivial cutoff interval yields an
  indifference score and a profitable-deviation interval.  For
  report-required testing, if `q̃ < q̄`, a Gaussian test score for some skill
  strictly between them clears `q̃` with probability strictly above one half.
- The continuous-law fairness surface is added for the Gaussian negative
  results, and the proof cores for Propositions 4.2--4.3 are proved from
  law-difference witnesses plus Gaussian mean/variance gaps.
- Proposition 4.2 now has a concrete conditional Gaussian posterior-score
  instantiation: strictly ordered latent skills give strictly ordered
  conditional posterior-score means.
- Proposition 4.3 now has concrete Gaussian posterior-score scale-gap
  instantiations over possibly different observed-feature sets, using the
  shared signal-precision-sum comparison from `GaussianOffsetSignalFamily`.
- `PaperInterface.lean` is the human-facing theorem statement ledger.
- Strategic withholding, fairness impossibility, observed-access
  strategy-proofness, and the final concrete equilibrium instantiations remain
  certificate-shaped.

## Fastest Proof Route

   posterior-score formula and one-score threshold interface are now shared;
   the next shared target is distribution-comparison lemmas.
2. Preserve the existing resampling proof path:
   `ConditionalResamplingExperiment`, `resampling_observableFair`, and
   `resampling_demographicallyFair`.
3. Build an observed-access threshold best-response interface for Lemma 4.1
   only after the posterior score formula and threshold comparison facts are
   available.  The one-score reporting cutoff wrapper is now available; the
   optional-reporting and report-required scalar deviation cores are now
   available.  The remaining strategic bridge is to connect those scalar
   deviation witnesses to the concrete equilibrium/no-profitable-deviation
   predicate and close the endpoint.
4. Continue instantiating the law-level Proposition 4.2 and Proposition 4.3
   cores with the paper's concrete Bayesian posterior laws.  The conditional
   posterior-score mean-gap and signal-precision scale-gap wrappers are now
   proved; the remaining work is to connect them to the concrete equilibrium
   and reporting model.
5. Treat Theorem 3.2 as a source-level fairness/test-blank implication and keep
   it separate from Gaussian calculus; it should consume a clean policy-surface
   or equilibrium certificate.

## Reusable Library Seams

- Conditional-kernel pushforward and demographic mixing facts already live in
  `EconCSLib.Foundations.Probability.Admissions`.
- Shared Gaussian posterior-score laws should live in
  `EconCSLib.Foundations.Probability.Gaussian`.
- Threshold best-response facts should be generic over one-dimensional scores
  and payoffs, then specialized in this paper.

## Validation

```bash
lake build LG21TestOptionalPolicies
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
```

Run the DAG command inside this folder.  Stage only explicit LG21 paths when
committing from the shared worktree.
