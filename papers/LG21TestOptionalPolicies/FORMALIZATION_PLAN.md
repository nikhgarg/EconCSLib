# LG21 Formalization Plan

Last updated: 2026-05-16


## Current State

- Finite admissions decompositions are proved in `MainTheorems.lean`.
- Definition 1 now has a concrete `(Y, X)` access-action object with `Y ≥ X`
  feasibility, optional-reporting/report-required regimes, source access
  student information `(q, base, test)`, source decision functions
  `Y(q, base)` and `X(base, test)`, and the feasibility/best-response/
  estimation-consistency projections encoded.  Binary reporting and taking
  subgames bridge `lg21Equilibrium` best responses to the
  no-profitable-deviation predicates used by Lemma 4.1.
- Definitions 2--5 now have direct PMF and continuous-law source predicates
  plus paper-interface unfold lemmas.  Definition 5 also has equivalent
  witness forms for concrete base/test relevance.
- Definition 6 and the finite distributional core of Theorem 4.4 are proved via
  the shared conditional-resampling API.  Definition 6 now explicitly unfolds
  both access and re-sampled no-access estimate laws as the same conditional
  test-score-law pushforward through the common estimate map.  Theorem 4.4
  also has a combined source-route wrapper that pairs the finite resampling
  fairness proof with the closed Lemma 4.1 observed-access source-action
  endpoint.
- The shared Bayesian Gaussian estimator algebra is proved:
  `paper_bayesian_optimal_estimator_gaussian` gives the precision-weighted
  posterior mean and marginal estimate law variance formula.
- Fixed-information reporting threshold support is proved:
  `paper_reporting_gaussian_threshold_iff_cutoff` turns posterior-estimate
  threshold decisions into explicit cutoffs in one reported feature/test score.
- Theorem 3.1 now has a concrete cutoff-strategy support lemma:
  `paper_theorem3_1_reporting_threshold_of_gaussian_best_response` packages
  the Gaussian reporting decision as a finite lower-cutoff rule and proves the
  monotonicity consequence for any such cutoff rule.  Its optional-reporting
  conclusions are now packaged in
  `LG21OptionalReportingStrategicWithholdingSourceWitness`, including the
  paper's all-take conclusion, finite score-threshold reporting at each base
  profile, and an explicit below-cutoff non-reporting score for base-indexed
  Gaussian posterior-threshold reporting.  The paper's optional-reporting
  nontriviality step is now formalized by
  `paper_theorem3_1_optional_reporting_gaussian_best_response_nontrivial`:
  two-sided best response plus the positive-slope Gaussian reported-score
  estimate rules out both everyone reporting and no one reporting.  The
  analogous report-required nontriviality step is
  `paper_theorem3_1_report_required_affine_best_response_nontrivial`, using
  positive-slope affine expected taking estimates to rule out both
  everyone taking/reporting and no one taking/reporting.  The paper's
  optional-reporting
  fixed-point/crossing step is now formalized by
  `paper_theorem3_1_optional_reporting_threshold_equilibrium_exists_of_crossing`:
  continuity plus opposite endpoint comparisons produce a finite indifferent
  reporting cutoff, and strict monotonicity proves reporting is optimal exactly
  above that cutoff.  The base-indexed wrapper
  `paper_theorem3_1_optional_reporting_source_witness_of_base_crossings`
  constructs the source-shaped all-take/threshold-reporting witness from these
  crossing hypotheses.  The analogous report-required crossing step is
  formalized by
  `paper_theorem3_1_report_required_threshold_equilibrium_exists_of_crossing`,
  and `paper_theorem3_1_report_required_source_witness_of_base_crossings`
  constructs a source-shaped finite skill-threshold witness for taking and
  reporting.  The wrappers
  `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_crossings`
  and
  `paper_theorem3_1_report_required_affine_source_witness_of_crossings`
  discharge the generic continuity/strict-monotonicity hypotheses for the
  optional Gaussian posterior estimate and the report-required affine expected
  taking estimate, respectively.  The policy-specific endpoints
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_source_witness`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_of_source_witness`
  now combine those optional-reporting/report-required source witnesses with
  concrete law-difference witnesses to rule out latent-skill, observable, and
  demographic fairness.  The older combined threshold conclusions are also
  packaged in
  `LG21StrategicWithholdingSourceWitness`.  Explicit base-indexed cutoff
  functions now construct this witness via
  `lg21ThresholdStrategicWithholdingSourceWitness`, including an explicit
  below-cutoff non-reporting score, and PMF/law wrappers prove failure of all
  three fairness criteria from concrete distribution-difference witnesses.
- Theorem 3.2 now has PMF and continuous-law endpoints, no-relevance forms,
  and contrapositive wrappers: test-blankness is equivalent to absence of a
  concrete base/test relevance witness, and such a witness rules out
  latent-skill or observable fairness once the source unraveling implication is
  available.
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
  The reporting-side cutoff premise is discharged for explicit Gaussian
  Bayesian threshold reporting policies by
  `paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_lower_tail_taking`,
  and the taking-side threshold premise is discharged for an explicit
  lower-tail taking threshold by
  `paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold`.
  The abstract lower-tail certificate has a concrete mathlib-backed
  standard-normal instantiation, `standardGaussianLowerTailMeanCertificate`.
  The final observed-access Lemma 4.1 action endpoint is now closed for the
  fully specified source models:
  `lg21FullySpecifiedOptionalReportingSourceEquilibriumData` and
  `lg21FullySpecifiedReportRequiredSourceEquilibriumData` encode the paper's
  Bayesian threshold games, and
  `paper_lemma4_1_observed_access_chosen_actions_of_fully_specified_source_models`
  proves that every source equilibrium chooses `(Y, X) = (1, 1)` in both
  optional-reporting and report-required regimes.
- The continuous-law fairness surface is added for the Gaussian negative
  results, and the proof cores for Propositions 4.2--4.3 are proved from
  law-difference witnesses plus Gaussian mean/variance gaps.
- Proposition 4.2 now has a concrete conditional Gaussian posterior-score
  instantiation: strictly ordered latent skills give strictly ordered
  conditional posterior-score means.  It also has a source-shaped
  `LG21EstimateLaw` wrapper for the point/Gaussian law surface used by the
  paper's distributional notation, plus fixed-base and base-indexed
  one-random-test posterior law surfaces matching the displayed proof formula.
  The concrete `lg21BaseIndexedOneTestPosteriorLawSurface` makes the no-access
  law identity definitional and proves the latent-skill unfairness endpoint
  without law-equality assumptions.  The paper's named route is now
  bridged as well: the Lemma 4.1 lower-tail all-report/all-take theorem feeds
  the fixed-base one-test posterior law to produce the Proposition 4.2
  latent-skill-fairness contradiction; the stronger wrappers use Lemma 4.1's
  explicit-threshold, binary-equilibrium, packaged threshold-equilibrium
  certificate, and fully specified observed-access source-action routes.
- Proposition 4.3 now has concrete Gaussian posterior-score scale-gap
  instantiations over possibly different observed-feature sets, using the
  shared signal-precision-sum comparison from `GaussianOffsetSignalFamily`.
  Its observable-fairness failure also has the source-shaped point-vs-Gaussian
  conditional law wrapper and fixed-base one-random-test posterior-law form.
  The paper's named route is now bridged through Lemma 4.1 as well: all-report
  and all-take feed the posterior-precision gap to rule out both observable and
  demographic fairness.  The concrete one-extra-test-signal precision gap is
  closed by the shared `GaussianOffsetSignalFamily.withExtraSignal` helper,
  and the strongest wrappers use Lemma 4.1's explicit-threshold,
  binary-equilibrium, packaged threshold-equilibrium-certificate, and fully
  specified observed-access source-action routes.  The concrete
  `lg21ExtraSignalPosteriorLawSurface` now makes the access and no-access
  observable/demographic laws definitional and proves the extra-signal
  observable/demographic unfairness endpoint without law-equality assumptions.
  The base-indexed observable surface
  `lg21BaseIndexedExtraSignalPosteriorLawSurface` proves observable unfairness
  at arbitrary nonempty base types.  The stronger
  `lg21BaseMixedExtraSignalPosteriorLawSurface` now represents demographic
  laws as finite mixtures over the common base-profile distribution and closes
  the observable/demographic unfairness endpoint through the fully specified
  observed-access source models.
- `PaperInterface.lean` is the human-facing theorem statement ledger.
- Strategic withholding and fairness impossibility remain certificate-shaped;
  observed-access strategy-proofness and Propositions 4.2--4.3 now route
  through fully specified source models.

## Fastest Proof Route

   posterior-score formula and one-score threshold interface are now shared;
   the next shared target is distribution-comparison lemmas.
2. Preserve the existing resampling proof path:
   `ConditionalResamplingExperiment`, `resampling_observableFair`, and
   `resampling_demographicallyFair`.  The current combined Theorem 4.4 wrapper
   should keep consuming `LG21GaussianThresholdEquilibriumCertificate` until
   the full source-equilibrium derivation is available.
3. Build an observed-access threshold best-response interface for Lemma 4.1
   only after the posterior score formula and threshold comparison facts are
   available.  The one-score reporting cutoff wrapper is now available; the
   optional-reporting scalar deviation core is now connected to an explicit
   source-shaped no-profitable-withholding contradiction, and the
   report-required scalar deviation witness is now connected to an explicit
   no-profitable-test-taking contradiction.  The current endpoint bridges prove
   all-report/all-take from the paper's "if not all, then finite cutoff" and
   lower-tail-mean premises; for Gaussian Bayesian threshold reporting, the
   reporting cutoff is now produced directly by the affine threshold lemma, and
   explicit lower-tail taking thresholds are supported.  The no-deviation facts
   now follow either from binary subgame equilibria, directly from source
   Definition 1 best-response projections, or from concrete source payoff
   models where the optional-reporting and report-required payoff identities
   are definitional.  Concrete threshold source models also make the reporting
   and taking threshold shapes definitional.  The fully specified source models
   now make the lower-tail no-report and no-test estimates definitional, and
   the source-model endpoint proves the paper's `(Y, X) = (1, 1)` conclusion.
   Remaining work should treat Lemma 4.1 as a closed input and connect this
   action endpoint to the concrete Proposition 4.2/4.3 source-law surfaces.
4. Continue instantiating the law-level Proposition 4.2 and Proposition 4.3
   cores with the paper's concrete Bayesian posterior laws.  The conditional
   posterior-score mean-gap and signal-precision scale-gap wrappers are now
   proved, and Propositions 4.2--4.3 are both routed through the closed Lemma
   4.1 source-action endpoint.  Proposition 4.2 now has a base-indexed concrete
   source-law surface with definitional no-access/access laws.  Proposition 4.3
   now has the analogous extra-signal concrete source-law surface with access
   law equal to `withExtraSignal` and no-access law equal to the base posterior
   law, plus a base-mixture endpoint whose demographic laws are finite mixtures
   over the shared base-profile distribution.  Proposition 4.3 should now be
   treated as closed; the next theorem-level work is Theorem 3.1 or Theorem 3.2.
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
