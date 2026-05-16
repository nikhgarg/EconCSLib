# LG21 Formalization Plan

Last updated: 2026-05-16


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
- Lemma 4.1 now has its two main scalar no-deviation contradictions
  formalized.  For optional reporting, a continuous strictly increasing
  reported-score estimate plus a non-report estimate inside a nontrivial cutoff
  interval yields an indifference score and a strictly profitable withheld
  score.  The Gaussian specialization now uses positive-slope posterior algebra
  to supply the low-score side automatically, so a nontrivial Gaussian
  reporting cutoff contradicts no-profitable-withholding as soon as the
  no-report estimate lies below the reported estimate at the cutoff.  For
  report-required testing, if `q̃ < q̄`, a Gaussian test score for some skill
  strictly between them clears `q̃` with probability strictly above one half;
  this now feeds the analogous theorem that a nontrivial taking cutoff
  contradicts no-profitable-test-taking.  Both cases now have conditional
  lower-tail endpoint bridges: if the source proof's monotonicity step supplies
  a finite cutoff whenever not everyone reports or takes, and the
  no-report/no-test estimate is identified with the shared
  `GaussianLowerTailMeanCertificate` lower-tail mean, the no-deviation
  contradictions imply all access students report and take.  These two cases
  are now combined in `paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds`.
  The abstract lower-tail certificate has a concrete mathlib-backed
  standard-normal instantiation, `standardGaussianLowerTailMeanCertificate`.
- The continuous-law fairness surface is added for the Gaussian negative
  results, and the proof cores for Propositions 4.2--4.3 are proved from
  law-difference witnesses plus Gaussian mean/variance gaps.
- Proposition 4.2 now has a concrete conditional Gaussian posterior-score
  instantiation: strictly ordered latent skills give strictly ordered
  conditional posterior-score means.  It also has a source-shaped
  `LG21EstimateLaw` wrapper for the point/Gaussian law surface used by the
  paper's distributional notation, plus the fixed-base one-random-test
  posterior law matching the displayed proof formula.  The paper's named route
  is now bridged as well: the Lemma 4.1 lower-tail all-report/all-take theorem
  feeds the fixed-base one-test posterior law to produce the Proposition 4.2
  latent-skill-fairness contradiction.
- Proposition 4.3 now has concrete Gaussian posterior-score scale-gap
  instantiations over possibly different observed-feature sets, using the
  shared signal-precision-sum comparison from `GaussianOffsetSignalFamily`.
  Its observable-fairness failure also has the source-shaped point-vs-Gaussian
  conditional law wrapper and fixed-base one-random-test posterior-law form.
  The paper's named route is now bridged through Lemma 4.1 as well: all-report
  and all-take feed the posterior-precision gap to rule out both observable and
  demographic fairness.  The concrete one-extra-test-signal precision gap is
  closed by the shared `GaussianOffsetSignalFamily.withExtraSignal` helper.
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
   optional-reporting scalar deviation core is now connected to an explicit
   source-shaped no-profitable-withholding contradiction, and the
   report-required scalar deviation witness is now connected to an explicit
   no-profitable-test-taking contradiction.  The current endpoint bridges prove
   all-report/all-take from the paper's "if not all, then finite cutoff" and
   lower-tail-mean premises.  The remaining strategic bridge is to derive those
   monotonicity-to-threshold/truncated-mean premises from the concrete
   equilibrium predicate and close the endpoint.
4. Continue instantiating the law-level Proposition 4.2 and Proposition 4.3
   cores with the paper's concrete Bayesian posterior laws.  The conditional
   posterior-score mean-gap and signal-precision scale-gap wrappers are now
   proved, and Propositions 4.2--4.3 are routed through Lemma 4.1's lower-tail
   bridge.  Proposition 4.3's one-extra-test-signal precision gap is no longer
   an assumption.  The remaining work is to connect both routes to the concrete
   equilibrium, threshold, and lower-tail assumptions.
5. Treat Theorem 3.2 as a source-level fairness/test-blank implication and keep
   it separate from Gaussian calculus; it should consume a clean policy-surface
   or equilibrium certificate.

## Reusable Library Seams

- Conditional-kernel pushforward and demographic mixing facts already live in
  `EconCSLib.Foundations.Probability.Admissions`.
- Shared Gaussian posterior-score laws and lower-tail conditional-mean
  interfaces should live in `EconCSLib.Foundations.Probability.Gaussian`;
  mathlib-backed standard-normal instantiations live in
  `EconCSLib.Foundations.Probability.GaussianMathlib`.
- Threshold best-response facts should be generic over one-dimensional scores
  and payoffs, then specialized in this paper.

## Validation

```bash
lake build LG21TestOptionalPolicies
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
```

Run the DAG command inside this folder.  Stage only explicit LG21 paths when
committing from the shared worktree.
