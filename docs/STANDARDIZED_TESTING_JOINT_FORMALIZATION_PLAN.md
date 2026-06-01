# Standardized Testing Joint Formalization Plan

Last updated: 2026-05-15

Scope:

- `papers/GLM20DroppingStandardizedTesting`
- `papers/LG21TestOptionalPolicies`

Both papers compare admissions policies built from latent skill, noisy observed
features, posterior estimates, and threshold decisions.  Treat them as one
campaign so the Gaussian/posterior/equilibrium infrastructure is proved once in
`EconCSLib` and consumed by thin paper wrappers.

## Shared Library First

Use existing probability modules before adding paper-local definitions:

- `EconCSLib.Foundations.Probability.Admissions`
- `EconCSLib.Foundations.Probability.Kernel`
- `EconCSLib.Foundations.Probability.Conditional`
- `EconCSLib.Foundations.Probability.Gaussian`
- `EconCSLib.Foundations.Probability.GaussianDerivatives`
- `EconCSLib.Foundations.Probability.RealDistribution`

Reusable targets that should live in the library:

1. Gaussian posterior scores for one or more independent signals:
   posterior mean, posterior variance, positive-affine score laws, and
   monotonicity in observed signals.
2. Threshold admissions accounting:
   tail mass, capacity equations, selected mean, and threshold monotonicity for
   finite mixtures of Gaussian posterior-score laws.
3. Conditional resampling and fairness:
   pushforward equality, demographic mixing, and finite conditional-kernel
   identities.  The LG21 re-sampling core already uses this path.
4. Strategic threshold predicates:
   reusable one-dimensional threshold best-response interfaces, with
   paper-local fields for concrete utilities and school objectives.

Keep paper folders as the audit layer: source notation, theorem names, and
conditional wrappers stay there.  Move only second-paper-useful facts to
`EconCSLib`.

## Joint Proof Order

1. Stabilize the folder contracts and DAGs for both papers.
   This is the current setup pass: add `PaperInterface.lean`, add live
   `FORMALIZATION_PLAN.md`, rebuild DAG PDFs, and verify root imports.
2. Close shared Gaussian posterior algebra in `EconCSLib`.
   The first reusable batch is done: finite-feature posterior means now have
   precision-weighted division forms and posterior-mean variance formulas, and
   both papers expose those facts through paper-facing wrappers.  The second
   reusable batch is also done: one-coordinate posterior scores are strictly
   increasing affine functions and crossing a posterior threshold is equivalent
   to crossing an explicit affine cutoff.  The third reusable batch is now
   done: posterior-mean variance and scale are strictly increasing in total
   signal precision, standard-normal median/tail facts are exposed through
   `StandardGaussianCDFAPI`, and Gaussian upper tails are strictly decreasing in
   the threshold.
3. Wire GLM20 Lemma 1 and LG21 posterior-estimate distribution facts into the
   concrete source policy surfaces.
4. Prove common threshold/tail accounting for posterior-score policies.
   Use it for GLM20 Proposition 1, Lemma 2, Theorems 1--2, and LG21
   Proposition 4.2 / Proposition 4.3.  The GLM20 Proposition 1(i)
  under-representation core is proved from a total-precision gap and selective
  capacity, its individual-fairness cutoff/failure core is proved from the
  Gaussian tail-difference formulas, its admitted-merit core is proved under
  the explicit scaled-hazard monotonicity certificate, its closed-form
  threshold/diversity comparative statics are proved from the displayed
  threshold formula, and its high-skill individual-fairness-gap comparative
  core is proved from a reusable square-root comparison lemma.  GLM20 Lemma 2
  now consumes reusable Gaussian CDF derivative wrappers and doubled-log
  standard-normal density wrappers for affine upper-tail formulas, so the
  the source limit `I(q; P_S) -> 0` now follows from a Gaussian tail-limit API.
  The remaining Lemma 2 debt is tying the abstract source-surface
  `individualFairnessGap` field to the conditional Gaussian probability
  formula.  LG21 now has a continuous-law fairness surface plus law-level
  Proposition 4.2 /
  Proposition 4.3 contradiction cores.
5. Separate strategic fixed-point work from Gaussian algebra.
   Build a reusable threshold-equilibrium certificate only after posterior and
   threshold comparisons are available.
6. Return to paper-facing wrappers and remove certificates one named theorem at
   a time.

## Paper-Specific Priorities

GLM20:

- Current source-faithful target: finish Proposition 1.  Part (i)'s static
  under-representation and group-fairness failure core is proved through
  `paper_proposition1_not_group_fair_of_precision_gap_capacity_lt_half`.
  Part (ii)'s individual-fairness failure/cutoff core is proved through
  `paper_proposition1_not_individual_fair_of_precision_tail_formulas`.
  Part (iii)'s admitted-merit core is proved through
  `paper_proposition1_groupB_academic_merit_lt_groupA_of_tail_mean`, and the
  three static conclusions are bundled in
  `paper_proposition1_fixed_policy_static_core`.  The paper's threshold and
  diversity-share comparative statics for larger informativeness gaps are
  proved through `paper_proposition1_diversity_share_decreases_of_precision_gap_lt`.
  The high-skill individual-fairness-gap comparative core is proved through
  `paper_proposition1_individual_fairness_gap_increases_of_precision_gap_high_skill_formula`.
  Remaining Proposition 1 work is source-surface wiring and discharging the
  hazard-backed admitted-merit analytic certificate.
- Lemma 2 now has its generic calculus and limit shell proved through
  `paper_lemma2_individual_fairness_gap_strictAntiOn_of_deriv_neg` and
  `paper_lemma2_individual_fairness_gap_tendsto_zero_of_tail_tendsto`, and its
  displayed `q_e` log-density algebra is proved through
  `paper_lemma2_log_density_inequality_of_q_gt_threshold`. These are packaged
  in `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_log_density_data`.
  The affine Gaussian upper-tail derivative/continuity bridge and the
  standard-normal doubled-log bridge are proved in
  `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_conditional_posterior_laws`.
  The limit `I(q; P_S) -> 0` is proved through
  `paper_lemma2_individual_fairness_gap_tendsto_zero_of_conditional_posterior_laws`,
  and `paper_lemma2_conditional_posterior_laws` packages both Lemma 2 clauses.
  The first Theorem 2(ii) seam is also proved:
  `paper_theorem2_group_admission_probability_decreases_iff_above_cutoff`
  shows that affine Gaussian upper-tail admission probabilities cross exactly
  above the paper's group-level cutoff. The no-barrier Theorem 2 support now
  also includes the individual-fairness gap aggregation lemma
  `paper_theorem2_individual_fairness_gap_full_gt_sub_of_delta_gt`, the
  selective-capacity threshold increase
  `paper_theorem2_admission_threshold_full_gt_sub_of_scale_increases`, and the
  group academic-merit tail-mean comparison
  `paper_theorem2_group_academic_merit_full_gt_sub_of_tail_mean`.
  Remaining Lemma 2 work is tying the abstract source-surface
  `individualFairnessGap` field to that conditional Gaussian probability
  formula.
- Then wire `paper_lemma1_estimated_skill_gaussian` into the concrete
  group/policy surface so the certificate endpoint is no longer needed for
  Lemma 1, and continue to Lemma 2 / Theorems 1--2.
- Strategic Section 5 should wait until the static Gaussian threshold layer is
  stable.

LG21:

- Theorem 4.4's finite resampling distributional core is already closed.
- The Bayesian Gaussian estimator formula/law is now exposed through
  `paper_bayesian_optimal_estimator_gaussian`; fixed-information reporting
  thresholds are exposed through `paper_reporting_gaussian_threshold_iff_cutoff`.
- Proposition 4.2 and Proposition 4.3 now have continuous-law proof cores:
  four-group latent-fairness contradiction, Gaussian mean-gap law difference,
  observable/demographic law witnesses, and Gaussian variance-gap contradictions.
- Observed-access Lemma 4.1 is closed through
  `paper_lemma4_1_strategy_proofness_of_certificate`, with source-model
  wrappers proving the paper's `(Y, X) = (1, 1)` conclusion.
- Theorem 3.1 now has short Section 3 paper-interface aliases over the
  strongest concrete continuous-law surfaces:
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding`.
  These state hidden access and return every-equilibrium strategic-withholding
  witnesses plus failures of all three fairness criteria.
- Theorem 3.2 now has short Section 3 paper-interface aliases over the
  concrete event-or-blank case-split surfaces:
  `paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility`,
  `paper_interface_theorem3_2_section3_report_required_fairness_impossibility`,
  and the matching no-relevance aliases.  The bridge
  `paper_interface_theorem3_2_positive_event_or_blank_of_no_positive_event_blank`
  now names the zero-positive-reporter/taker-implies-blank branch used to build
  the case split.  A stricter conditional-kernel version is optional only if
  the target statement is broadened beyond the current concrete constant-latent
  event-share surfaces.

## Validation Commands

After setup or declaration-level edits:

```bash
lake build GLM20DroppingStandardizedTesting
lake build LG21TestOptionalPolicies
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
```

Run the `latexmk` command inside each paper folder.  The source PDFs and DAG PDFs
are locally ignored unless already tracked; commit TeX/Lean/README/plan changes
explicitly and avoid sweeping unrelated dirty files.
