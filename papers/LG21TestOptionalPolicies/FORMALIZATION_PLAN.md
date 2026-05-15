# LG21 Formalization Plan

Last updated: 2026-05-15


## Current State

- Finite admissions decompositions are proved in `MainTheorems.lean`.
- Definition 6 and the finite distributional core of Theorem 4.4 are proved via
  the shared conditional-resampling API.
- The shared Bayesian Gaussian estimator algebra is proved:
  `paper_bayesian_optimal_estimator_gaussian` gives the precision-weighted
  posterior mean and marginal estimate law variance formula.
- Fixed-information reporting threshold support is proved:
  `paper_reporting_gaussian_threshold_iff_cutoff` turns posterior-estimate
  threshold decisions into explicit cutoffs in one reported feature/test score.
- The continuous-law fairness surface is added for the Gaussian negative
  results, and the proof cores for Propositions 4.2--4.3 are proved from
  law-difference witnesses plus Gaussian mean/variance gaps.
- `PaperInterface.lean` is the human-facing theorem statement ledger.
- Strategic withholding, fairness impossibility, observed-access
  strategy-proofness, and negative fairness propositions remain
  certificate-shaped.

## Fastest Proof Route

   posterior-score formula and one-score threshold interface are now shared;
   the next shared target is distribution-comparison lemmas.
2. Preserve the existing resampling proof path:
   `ConditionalResamplingExperiment`, `resampling_observableFair`, and
   `resampling_demographicallyFair`.
3. Build an observed-access threshold best-response interface for Lemma 4.1
   only after the posterior score formula and threshold comparison facts are
   available.
4. Instantiate the law-level Proposition 4.2 and Proposition 4.3 cores with the
   paper's concrete Bayesian posterior laws.  The logical contradiction layer
   and Gaussian law-difference lemmas are already proved.
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
