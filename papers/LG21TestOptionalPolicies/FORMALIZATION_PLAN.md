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
  no-profitable-deviation predicates used by Lemma 4.1.  The concrete
  optional-reporting and report-required source payoff models also now supply
  full two-sided binary best-response predicates for Theorem 3.1 and
  Theorem 3.2.  The optional-reporting and report-required payoff models now
  also have base-indexed variants matching the paper's dependence on non-test
  features, with their own two-sided best-response bridges.
- Definitions 2--5 now have direct PMF and continuous-law source predicates
  plus paper-interface unfold lemmas.  Definition 5 also has equivalent
  witness forms for concrete base/test relevance and named observable-identity
  certificates for the ordinary full-feature/base-only surface bridge to
  Definition 3.
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
  follow-on bridge
  `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_best_response_tiebreak`
  packages the report-at-indifference convention into a source-shaped finite
  reporting-cutoff witness.  The cutoff-indexed no-report estimate formula is
  now partially source-instantiated: `lg21OptionalNoReportMixtureEstimate`
  encodes the unobserved-access pool of no-access students and access students
  below the reporting cutoff, and
  `paper_theorem3_1_optional_no_report_mixture_standard_lower_tail_continuous`
  proves continuity for the Gaussian lower-tail posterior component under
  `0 ≤ C < 1`; the specialized crossing wrapper
  `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_crossings`
  now consumes only the finite endpoint inequalities for that source formula.
  The
  analogous report-required nontriviality step is
  `paper_theorem3_1_report_required_affine_best_response_nontrivial`, using
  positive-slope affine expected taking estimates to rule out both
  everyone taking/reporting and no one taking/reporting.  Its follow-on bridge
  `paper_theorem3_1_report_required_affine_source_witness_of_best_response_tiebreak`
  packages the take-at-indifference convention into a source-shaped finite
  skill-cutoff witness.  The analogous no-take mixture continuity and crossing
  wrapper are
  `paper_theorem3_1_report_required_no_take_mixture_standard_lower_tail_continuous`
  and
  `paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture_crossings`;
  these leave only finite endpoint inequalities for the report-required source
  formula.  The generic mixture endpoint algebra
  `lt_lg21OptionalNoReportMixtureEstimate_of_lt_components` and
  `lg21OptionalNoReportMixtureEstimate_lt_of_components_lt` now reduces those
  finite endpoint comparisons to component-wise comparisons when both
  components are on the same side of the target.  The exact weighted-gap
  variants
  `lt_lg21OptionalNoReportMixtureEstimate_of_weighted_gap_pos` and
  `lg21OptionalNoReportMixtureEstimate_lt_of_weighted_gap_neg` handle the
  low-endpoint case where the access lower-tail component can be below the
  target but has small Gaussian mass.  The Gaussian Mills/symmetry bridge
  `standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot` proves that
  this CDF-weighted lower-tail correction vanishes in the far left tail, and
  `paper_theorem3_1_affine_lower_tail_mixture_low_endpoint_exists` closes the
  generic affine low endpoint.  Its optional/report-required specializations
  are
  `paper_theorem3_1_optional_no_report_mixture_low_endpoint_exists` and
  `paper_theorem3_1_report_required_no_take_mixture_low_endpoint_exists`.
  The high-endpoint inequalities for both policy regimes are closed by
  `paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists` and
  `paper_theorem3_1_report_required_no_take_mixture_high_endpoint_exists`:
  the reported/take payoff eventually exceeds the base-only component, and the
  Gaussian lower-tail component is always strictly below the cutoff payoff.
  The after-low variants
  `paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists_after` and
  `paper_theorem3_1_report_required_no_take_mixture_high_endpoint_exists_after`
  show that this high endpoint can be chosen above any supplied finite low
  cutoff.  Consequently the source-mixture wrappers
  `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_low_endpoint`
  and
  `paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture_low_endpoint`
  expose the former low-endpoint-only boundary, while
  `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture`
  and
  `paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture`
  now choose both endpoints automatically.  The paper's
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
  concrete distribution-difference witnesses to rule out latent-skill,
  observable, and demographic fairness.  The closed source-mixture variants
  `paper_theorem3_1_optional_reporting_strategic_withholding_of_no_report_mixture`,
  `paper_theorem3_1_report_required_strategic_withholding_of_no_take_mixture`,
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture`
  now remove the source-witness certificate on both the PMF and law surfaces,
  leaving only those concrete distribution-difference witnesses as inputs.  The
  concrete base-indexed one-test posterior law surface now supplies those law
  witnesses directly: `paper_base_indexed_one_test_posterior_source_law_not_observably_fair`,
  `paper_base_indexed_one_test_posterior_source_law_not_demographically_fair`,
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_indexed_one_test_posterior_surface`,
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_base_indexed_one_test_posterior_surface`
  combine the automatic source-mixture cutoffs with Gaussian-vs-point
  latent/observable/demographic law differences.  The concrete Gaussian
  posterior-law surface wrappers
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_gaussian_posterior_surface`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_affine_skill_posterior_surface`
  now remove the arbitrary posterior-surface parameters from the continuous-law
  route.  `LG21SkillBaseMixtureEstimateLaw`,
  `lg21BaseMixedGaussianPosteriorLawSurface`, and
  `lg21BaseMixedAffineSkillPosteriorLawSurface` now close the stricter
  conditional-on-skill continuous-law route: observable access laws are symbolic
  latent-skill mixtures, and demographic laws are symbolic base-profile
  mixtures.  The new optional-reporting and report-required base-mixed
  endpoints combine those surfaces with the automatic source-mixture cutoffs.
  `LG21LawStrategicWithholdingCertificate` now mirrors the compact PMF
  certificate endpoint for these continuous-law routes.  The generic PMF and
  continuous-law source-witness routes now build the corresponding compact
  strategic-withholding certificates directly.
  Theorem 3.1 now also has regime-specific optional-reporting and
  report-required PMF/law certificates:
  `LG21OptionalReportingStrategicWithholdingCertificate`,
  `LG21LawOptionalReportingStrategicWithholdingCertificate`,
  `LG21ReportRequiredStrategicWithholdingCertificate`, and
  `LG21LawReportRequiredStrategicWithholdingCertificate`.  These preserve the
  paper's exact optional-reporting conclusion, all access students take and
  reporting is thresholded, instead of routing optional reporting through the
  generic finite-taking-threshold certificate.
  The strongest concrete source-shaped continuous-law surfaces now construct
  those regime-specific certificates directly via
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_certificate_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_certificate_of_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`.
  They now also have finite-event-share variants,
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_certificate_of_event_share_no_report_mixture_and_base_mixed_gaussian_posterior_surface`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_certificate_of_event_share_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`,
  which derive `0 <= C < 1` directly from PMF nonnegativity plus positive
  no-access complement mass.
  The continuous-law route now also has explicit `∀ e` wrappers for
  equilibrium-indexed source quantities:
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_certificate_for_every_equilibrium_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_certificate_for_every_equilibrium_of_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`.
  The finite-event-share variants
  `paper_theorem3_1_optional_reporting_law_strategic_withholding_certificate_for_every_equilibrium_of_event_share_no_report_mixture_and_base_mixed_gaussian_posterior_surface`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_certificate_for_every_equilibrium_of_event_share_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`
  instantiate those `∀ e` certificate families from finite student laws and
  positive-mass no-access complement events.
  The Section 3 event-share endpoints now also have full-support/not-all-acting
  wrappers:
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_event_share_of_full_support_not_all`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding_event_share_of_full_support_not_all`
  derive the positive-mass complement event from full support of the finite
  cohort law plus an ordinary witness outside the reporting/taking event.
  The reusable event-share bridge itself is public as
  `paper_interface_theorem3_2_pmf_event_share_fn_complement_mass_of_full_support_not_all`
  and
  `paper_interface_theorem3_2_pmf_event_share_fn_lt_one_of_full_support_not_all`.
  Theorem 3.1 now also has Section 3 hidden-access wrappers over PMF and
  continuous-law regime-specific certificates, including every-equilibrium
  certificate-family forms.  The access-status hypothesis is exposed as
  `LG21SchoolInformationSet.fromAccessAction false ... = none`, and the
  wrappers then return the optional-reporting or report-required
  strategic-withholding/fairness conclusions.  The concrete base-mixed
  continuous-law route now also has final short Section 3 paper-interface
  endpoints:
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding`.
  Their finite-event-share variants,
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_of_event_share_no_report_mixture_and_base_mixed_gaussian_posterior_surface`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding_of_event_share_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`,
  remove the explicit `accessFraction`/`0 <= C < 1` premises from the public
  Section 3 endpoints.  The shorter aliases
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_event_share`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding_event_share`
  state the same finite-event-share route without the long implementation
  suffix.
  These avoid certificate-field indirection by directly returning, for every
  equilibrium index, the optional/report-required strategic-withholding witness
  and failures of all three fairness notions on the concrete Gaussian or
  affine-skill posterior law surface.  The finite-event-share PMF route is also
  proved by
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_pmf_of_event_share_no_report_mixture`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding_pmf_of_event_share_no_take_mixture`,
  which instantiate the access fraction from a finite student event and derive
  `0 <= C < 1` internally.  The matching every-equilibrium PMF endpoints
  `paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_pmf_for_every_equilibrium_of_event_share_no_report_mixture`
  and
  `paper_interface_theorem3_1_section3_report_required_strategic_withholding_pmf_for_every_equilibrium_of_event_share_no_take_mixture`
  now return one strategic-withholding witness per equilibrium index.  A fully
  concrete finite PMF surface remains optional if that representation is
  desired.  The
  older combined threshold conclusions are also
  packaged in
  `LG21StrategicWithholdingSourceWitness`.  Explicit base-indexed cutoff
  functions now construct this witness via
  `lg21ThresholdStrategicWithholdingSourceWitness`, including an explicit
  below-cutoff non-reporting score, and PMF/law wrappers prove failure of all
  three fairness criteria from concrete distribution-difference witnesses.
  The finite event-share layer now has strict complement-mass bounds:
  `lg21PMFEventShare_lt_one_of_mass_not` and
  `lg21PMFEventShareFn_lt_one_of_mass_not` prove that a positive-mass atom
  outside the reporter/taker event makes the corresponding finite share
  strictly below one, giving a reusable route to the `accessFraction < 1`
  premise in source-mixture instantiations.  The wrappers
  `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_event_share_no_report_mixture`
  and
  `paper_theorem3_1_report_required_affine_source_witness_of_event_share_no_take_mixture`
  use that route directly, instantiating the access fraction as a finite PMF
  event share and deriving `0 ≤ C < 1` from the PMF and positive complement
  mass.
- Theorem 3.2 now has PMF and continuous-law endpoints, no-relevance forms,
  and contrapositive wrappers: test-blankness is equivalent to absence of a
  concrete base/test relevance witness, and such a witness rules out
  latent-skill or observable fairness once the source unraveling implication is
  available.  These certificate and no-relevance endpoints now also have
  Section 3 hidden-access wrappers over PMF and continuous-law surfaces, so the
  paper hypothesis that the school does not observe access status is exposed
  directly beside the fairness-impossibility conclusion.  The
  certificate-packaged optional-reporting and report-required event-share
  source-equilibrium routes now have matching Section 3 implication and
  no-relevance wrappers.  The same source-equilibrium layer now has the paper's
  event-or-blank case split: a local positive reporter/taker share gives the
  unraveling contradiction, while the no-positive-share branch is supplied by
  `lg21EventSharePositiveOrBlank_of_no_positive_event_implies_blank` or, in
  share language, by
  `lg21EventSharePositiveOrBlank_of_zero_event_share_implies_blank`.
  These convert the paper convention "no one reports/takes, hence test-blank"
  into the direct test-blankness assumption for that equilibrium/base profile.
  Definition 5's no-reporter/no-taker branch now has explicit endpoints
  `lg21SourceTestBlank_of_no_positive_event_blank` and
  `lg21SourceTestBlank_of_zero_event_share_blank`, plus the constructed
  blank-on-zero-share global equality
  `lg21FullFeatureEstimateBlankOnZeroEventShare_testBlank_of_zero_share`.
  The blank-on-zero constructor also now has raw-preservation and raw
  no-relevance endpoints:
  `lg21FullFeatureEstimateBlankOnZeroEventShare_eq_raw_of_nonzero_share`,
  `lg21FullFeatureEstimateBlankOnZeroEventShare_eq_raw_of_positive_event`,
  `lg21FullFeatureEstimateBlankOnZeroEventShare_no_raw_relevance_of_no_normalized_relevance`,
  and
  `lg21FullFeatureEstimateBlankOnZeroEventShare_no_raw_relevance_of_positive_event`.
  It now also has exact equivalence endpoints
  `lg21FullFeatureEstimateBlankOnZeroEventShare_no_normalized_relevance_iff_no_raw_relevance_on_nonzero_share`
  and
  `lg21FullFeatureEstimateBlankOnZeroEventShare_no_normalized_relevance_iff_no_raw_relevance_on_positive_event`.
  Thus the constructed surface is auditable both as a zero-share normalization
  and as an unchanged raw full-feature law on nonzero/positive-event profiles;
  raw no-relevance on those preserved profiles is exactly normalized
  no-relevance for the constructed law.  The paper-interface layer now combines
  those equivalences with the Section 3 fairness/no-relevance iff routes, giving
  direct optional-reporting and report-required endpoints where fairness is
  equivalent to raw no-relevance on nonzero-share or positive-event profiles.
  These make the source proof's "no one reports/takes" sentence separately
  auditable from the positive-share contradiction.  The other source-proof
  branch, "test-blank policies meet observable fairness trivially", is now
  exposed by `lg21_sourceObservablyFair_of_testBlank_of_fullFeature_baseOnly`
  and the continuous-law analogue; the named certificates
  `LG21FullFeatureBaseOnlyObservableIdentities` and
  `LG21LawFullFeatureBaseOnlyObservableIdentities` package the necessary
  source-surface identities for audit callers.  Combining those bridges with the
  fairness-impossibility certificates now gives PMF and continuous-law iff
  endpoints:
  `paper_theorem3_2_fairness_iff_test_blank_of_certificate_and_full_feature_base_only`,
  `paper_theorem3_2_observable_fair_iff_test_blank_of_certificate_and_full_feature_base_only`,
  and the corresponding law and Section 3 wrappers.  The parallel
  `_and_observableIdentities` wrappers consume the named certificate rather
  than separate `testOf`, access, and no-access identity arguments.  These
  state the paper's "only way" reading directly whenever the observable surface
  is the ordinary full-feature/base-only one.  The no-relevance iff wrappers
  `paper_theorem3_2_fairness_iff_no_test_relevance_of_certificate_and_full_feature_base_only`
  and its law analogue rephrase the same result as absence of any concrete
  base/test relevance witness, with Section 3 variants bundling the hidden
  access-status hypothesis.
  The source-equilibrium event-or-blank and zero-share routes now specialize
  those iff wrappers directly, giving Section 3 fairness/test-blank and
  fairness/no-relevance iff endpoints for both optional-reporting and
  report-required source certificates.  The event-or-blank and zero-share
  source routes now also have `_and_observableIdentities` variants that
  consume the named full-feature/base-only certificate directly.  These
  certificates can be built uniformly for binary-mixture and finite
  event-share surfaces via
  `lg21BinaryMixtureEstimateSurface_observableIdentities` and
  `lg21EventShareBinaryMixtureEstimateSurface_observableIdentities`.  These
  case-split endpoints also have
  Section 3 hidden-access wrappers, removing the earlier global positive-share
  assumption from the source-facing theorem route.  The fully concrete optional
  posterior-payoff and report-required
  unit-centered routes now factor out their source-equilibrium certificates and
  have Section 3 event-or-blank wrappers, so the positive-share versus
  already-test-blank split is available at the strongest concrete surfaces in
  both regimes.  Those concrete event-or-blank routes now also have
  Section 3 fairness/test-blank and fairness/no-relevance iff wrappers under
  the named full-feature/base-only observable-identity certificate; their Lean
  proofs call the certificate-consuming source routes directly.  The
  corresponding blank-on-zero-share concrete routes have direct Section 3 iff
  wrappers too, using the constructor-backed source certificate and
  observable-identity certificate to discharge the zero-share branch by
  definition.  The fully concrete
  optional posterior-payoff and
  report-required unit-centered constant-latent event-share surfaces now also
  have direct Section 3 wrappers, so the strongest current source-facing
  Theorem 3.2 endpoints expose hidden access and the
  fairness-implies-test-blankness conclusion together.  The
  source proof's positive-share resampling algebra is also
  formalized: `lg21_pmf_mixture_cancel_right` and
  `lg21_extensional_law_mixture_cancel_right` prove the displayed
  `D0 = λ D1 + (1 - λ) D0 ⇒ D1 = D0` step, and the theorem-facing wrappers turn
  observable fairness plus the access/no-access mixture identities into the
  reporter/no-reporter law equality.  The affine payoff comparison
  `paper_theorem3_2_affine_resampling_mean_payoff_lt` and the below-mean actor
  wrappers now prove the profitable-deviation contradiction whenever the full
  policy model supplies a currently acting score/skill below the resampling
  mean.  The direct unfairness wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_mixture_and_below_mean_actor`
  and
  `paper_theorem3_2_not_law_latent_or_observable_fair_of_observable_implication_and_below_mean_actor`
  expose this branch without requiring finite atoms.  The PMF and law logical
  bridges
  `paper_theorem3_2_fairness_implies_test_blank_of_not_latent_or_observable_fair`
  and
  `paper_theorem3_2_law_fairness_implies_test_blank_of_not_latent_or_observable_fair`
  convert such contradiction-style branches back into Theorem 3.2's
  fairness-implies-test-blankness shape.  The certificate constructors
  `paper_theorem3_2_fairness_impossibility_certificate_of_not_latent_or_observable_fair`
  and its law analogue now package those contradiction branches directly as
  `LG21FairnessImpossibilityCertificate` values for the generic Section 3 and
  iff wrappers.  The optional-reporting
  and report-required source-model wrappers derive the two-sided best-response
  field from concrete Definition 1 equilibria.  The cutoff-midpoint wrappers
  connect the existing threshold-strategy infrastructure to this direct branch:
  if the acting cutoff is below the resampling mean, the midpoint reports/takes
  and is still below mean.  The contrapositive cutoff wrappers now record the
  resulting necessary condition: under the source payoff/mixture hypotheses and
  latent-or-observable fairness, any stable threshold cutoff is weakly above
  the acting mean.  The finite actor-support branch now proves cutoff below
  the acting mean from the paper's finite "exists by the mean" intuition when
  all positive acting support lies weakly above the cutoff and some positive
  mass lies strictly above it.  The witness-level midpoint bridges prove the same
  below-mean reporter/taker existence fact directly for the Theorem 3.1
  optional-reporting and report-required threshold source witnesses, and the
  witness-level cutoff lower-bound wrappers connect those witnesses back to the
  concrete source decisions to derive the same necessary condition.  The
  Gaussian/all-report and Gaussian/all-take
  wrappers instantiate the paper's "such a student always exists" sentence by
  selecting `mean - scale` from a nondegenerate `GaussianScaleLaw`, avoiding
  point-mass assumptions in the continuous route.  The standard-Gaussian
  upper-tail wrappers now cover thresholded Gaussian acting cohorts directly:
  the Mills/hazard proof shows the upper-tail conditional mean at a cutoff is
  strictly above that cutoff, so the cutoff-midpoint branch applies.  The
  witness-level upper-tail wrappers connect the Theorem 3.1 optional-reporting
  and report-required threshold witnesses back to concrete source decisions and
  discharge the same impossibility branch for continuous Gaussian acting
  cohorts.  The source-witness upper-tail wrappers now extract the relevant
  finite cutoff from the witness itself, reducing the remaining policy-specific
  assumptions to decision identification and actor-mean/upper-tail-mean
  identification.  The best-response source-witness wrappers now build those
  witnesses from the concrete reporting/taking decisions via the Theorem 3.1
  best-response and tie-breaking constructors, so the decision-identification
  side is closed for that route.  The remaining continuous-route source
  obligation is the policy-specific actor-mean/upper-tail-mean identification.
  The threshold-actor-mean endpoints close that obligation for normalized
  source models whose acting mean is definitionally the Gaussian upper-tail
  mean at a concrete reporting/taking threshold, using the reusable
  `lowerThresholdCutoff_unique` lemma from `EconCSLib`.  The source-equilibrium
  upper-tail wrappers now derive the best-response premises from the concrete
  base-indexed optional/report-required source games, leaving the Gaussian
  payoff identity, tie-breaking convention, threshold shape, and mixture
  identities as the visible source assumptions for this route.  The packaged
  certificates
  `LG21OptionalReportingGaussianUpperTailSourceEquilibriumCertificate` and
  `LG21ReportRequiredUpperTailSourceEquilibriumCertificate`, with wrappers
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_source_equilibrium`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_source_equilibrium`,
  make this route auditable: persistent source-model assumptions live in the
  certificate, while theorem-local data are the reporter/no-reporter mixture
  comparison and, in the report-required case, the outside-payoff equality after
  reporter/no-reporter equality.  The binary-mixture wrappers
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_binary_mixture_source_equilibrium`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_binary_mixture_source_equilibrium`
  derive the displayed mixture comparison directly from `lg21BinaryMixturePMF`.
  The event-share variants
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_source_equilibrium`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_source_equilibrium`
  derive `λ > 0` from a finite positive-mass reporter/taker event.  The generic
  surfaces `lg21BinaryMixtureEstimateSurface` and
  `lg21EventShareBinaryMixtureEstimateSurface`, together with
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_surface`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_surface`,
  make the no-access and observable-access mixture identities definitional for
  arbitrary PMF-valued base-only/full-feature estimates.  The constant-latent
  surface variants
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_constant_latent_surface`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface`
  further discharge the latent-to-observable identities via
  `lg21LatentSkillEstimateDistribution_const_indexed`.  The optional-reporting
  posterior-payoff specialization
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`
  now takes the reported and no-report source payoffs directly as Gaussian
  posterior means and derives the affine certificate fields internally from
  `GaussianOffsetSignalFamily.posteriorMean_update_eq_base_add_weight_mul`.
  Its tie-at-indifference step is now proved internally from strict posterior
  monotonicity and the Gaussian upper-tail-mean-above-threshold lemma.  The
  companion implication wrapper
  `paper_theorem3_2_optional_reporting_fairness_implies_test_blank_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`
  presents this continuous route directly as fairness implies test-blankness.
  The nonempty-equilibrium constructor
  `paper_theorem3_2_optional_reporting_fairness_impossibility_certificate_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff_of_nonempty_equilibrium`
  now packages this concrete optional surface into the compact
  `LG21FairnessImpossibilityCertificate` interface.
  The report-required
  centered-base-term endpoint
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface_centered_baseTerm`
  closes the outside-payoff equality by defining the report-required base term
  as `denom / 2 - signalWeight * upperTailMean`.  The report-required
  affine-centered-payoff endpoint
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface_affine_centered_payoff`
  specializes this to denominator `1`, with source payoff stated directly as
  `1 / 2 - slope * upperTailMean + slope * skill`.  Its tie-at-indifference
  step is now proved internally: indifference forces `skill = upperTailMean`,
  and the Gaussian upper-tail mean is strictly above the decision threshold.
  The unit-centered endpoint
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`
  specializes further to source payoff
  `1 / 2 - upperTailMean + skill`, removing the slope parameter too.  The
  implication wrapper
  `paper_theorem3_2_report_required_fairness_implies_test_blank_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`
  presents this normalized report-required route directly in Theorem 3.2's
  fairness-implies-test-blankness form.  Its nonempty-equilibrium constructor
  `paper_theorem3_2_report_required_fairness_impossibility_certificate_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff_of_nonempty_equilibrium`
  now packages the concrete unit-centered report-required surface into the same
  compact certificate interface.
  The direct Section 3 positive-share no-relevance wrappers
  `paper_theorem3_2_section3_optional_reporting_no_test_relevance_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff_of_nonempty_equilibrium`
  and
  `paper_theorem3_2_section3_report_required_no_test_relevance_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff_of_nonempty_equilibrium`
  bundle hidden access with the corresponding nonempty-equilibrium
  no-relevance endpoints, so audit callers can use the concrete positive-share
  surfaces without going through the broader event-or-blank case split.
  The companion Section 3 iff wrappers
  `paper_theorem3_2_section3_optional_reporting_fairness_iff_test_blank_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`,
  `paper_theorem3_2_section3_optional_reporting_fairness_iff_no_test_relevance_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`
  and
  `paper_theorem3_2_section3_report_required_fairness_iff_test_blank_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`,
  `paper_theorem3_2_section3_report_required_fairness_iff_no_test_relevance_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`
  specialize the generic iff route to those concrete positive-share surfaces,
  leaving only the standard full-feature/base-only observable-law identity
  certificate explicit.
  The
  finite acting-distribution
  lemmas
  `paper_theorem3_2_exists_support_actor_le_mean` and
  `paper_theorem3_2_exists_support_actor_lt_mean_of_exists_mean_lt_actor`
  formalize the paper's mean-existence claim, with the important strictness
  caveat: strict profitable deviation needs a nondegenerate acting distribution
  with some positive-mass actor above the mean.  The nondegenerate actor
  distribution wrappers combine this support fact with the resampling
  cancellation and payoff comparison.  The best-response wrappers
  `paper_theorem3_2_observable_fair_best_response_forces_no_above_mean_actor`
  and
  `paper_theorem3_2_law_observable_fair_best_response_forces_no_above_mean_actor`
  now turn that instability around: observable fairness plus two-sided best
  response rules out positive mass above the acting distribution mean.  The
  companion finite support bridge
  `paper_theorem3_2_no_above_mean_actor_forces_support_at_mean` and the PMF/law
  wrappers
  `paper_theorem3_2_observable_fair_best_response_forces_actor_support_at_mean`
  and
  `paper_theorem3_2_law_observable_fair_best_response_forces_actor_support_at_mean`
  strengthen this to: every positive-mass actor must sit exactly at the acting
  distribution mean.  The finite bridge
  `paper_theorem3_2_support_at_mean_forces_no_distinct_positive_mass_actor_values`
  and its PMF/law wrappers now additionally prove that observable fairness plus
  two-sided best response rules out two positive-mass actors with distinct
  values.  The PMF/law bridges
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`
  and
  `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`
  now turn this into observable fairness implies test-blankness once the full
  source model supplies the final non-test-blank-to-distinct-positive-mass-actor
  witness.  The off-mean variants
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`
  and
  `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`
  reduce the final source obligation to one positive-mass acting type whose
  value differs from the acting-distribution mean.  The source-shaped witness
  structures `LG21ObservableFairTestBlankSourceWitness` and
  `LG21LawObservableFairTestBlankSourceWitness` now package the mixture,
  best-response, payoff, and off-mean obligations.  They feed
  `paper_theorem3_2_fairness_impossibility_of_mixture_and_source_witness` and
  `paper_theorem3_2_law_fairness_impossibility_of_observable_implication_and_source_witness`,
  giving paper-facing Theorem 3.2 endpoints without the old tautological
  fairness-impossibility certificate.  The point-estimate constructors
  `paper_theorem3_2_nonblank_off_mean_witness_of_point_estimate_surface` and
  `paper_theorem3_2_law_nonblank_off_mean_witness_of_point_estimate_surface`
  discharge the off-mean field for deterministic scalar PMF/point-law surfaces
  where the base-only estimate is the acting mean and the full-feature estimate
  is the selected actor value.  The direct point-estimate endpoints
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_point_estimate_source`
  and
  `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_point_estimate_source`
  combine that constructor with the mixture, best-response, and affine-payoff
  bridge.  The optional-reporting and report-required point-estimate wrappers
  now derive the needed two-sided best-response predicate directly from the
  concrete source equilibrium models.  The PMF binary-mixture helper
  `lg21BinaryMixturePMF` now supplies the positive-share reporter/no-reporter
  mixture identity for source surfaces that define observable-access estimates
  with a Bernoulli share.  The optional-reporting and report-required
  point-estimate endpoints now combine this binary-mixture wrapper with the
  concrete Definition 1 best-response bridge.  The base-indexed
  optional-reporting affine endpoint now also makes the paper's reported-score
  and no-report payoff identities definitional.  The concrete binary-mixture
  point-estimate surface now makes the observable mixture, no-access,
  base-only, and full-feature point-estimate identities definitional too.  The
  concrete fairness endpoint now combines this surface route with the
  latent-to-observable mixture reduction, and the `_self_law` wrapper uses the
  reporter/no-reporter PMFs themselves to eliminate the redundant abstract-law
  equality bridge.  The base-indexed report-required affine endpoint now makes
  the paper's taking payoff formula definitional, and the concrete
  report-required fairness endpoint routes it through the same binary-mixture
  point-estimate surface and latent-to-observable mixture reduction.  The
  centered-outside variant reduces the report-required outside-payoff identity
  to the algebraic condition that the affine numerator at the resampling mean
  is half the denominator.  The point-estimate unfairness wrapper now converts
  these fairness-to-test-blank routes into direct latent-or-observable
  unfairness from an explicit off-mean test witness, and the optional-reporting
  concrete direct endpoint applies it to the optional binary-mixture surface.
  The report-required concrete direct endpoint applies it under the centered
  outside-payoff identity.  The distinct-tests bridge turns two different
  full-feature point estimates at one base profile into the off-mean witness
  needed by the direct unfairness endpoints, and the concrete optional and
  report-required distinct-test endpoints expose that paper-facing relevance
  condition directly on the binary-mixture point-estimate surfaces.  The
  localized supported-test variants now use the no-distinct-positive-mass
  actor route directly, reducing the actor-support obligation to the two
  displayed tests rather than requiring every test in the feature space to map
  to a positive-mass actor.  The event-share helpers `lg21PMFEventShare`,
  `lg21PMFEventShare_le_one`, and `lg21PMFEventShare_pos_of_mass` now turn
  finite reporter/taker event probabilities into the `NNReal` shares used by
  the binary-mixture surface, so the share upper bound and strict positivity
  reduce to ordinary finite event-mass facts.  The event-share concrete
  endpoints wire those shares directly into the optional-reporting and
  report-required binary-mixture surfaces.  The report-required centered
  base-term endpoint replaces the centered-numerator outside-payoff premise
  with the auditable identity
  `baseTerm = denom / 2 - signalWeight * mean`.  The constant-latent
  event-share endpoints now discharge the latent-to-observable mixture
  identities for the concrete optional/report-required surfaces when the
  latent kernels are skill-independent copies of the observable laws.  The
  remaining concrete policy obligations are the two displayed support facts
  and the report-required centered base-term identity.  The mapped-actor-law
  event-share endpoints further reduce those displayed support facts to
  positive mass of the displayed concrete test/skill values under a
  pushforward acting law.  The centered-base-term specialization defines the
  report-required base term as `denom / 2 - signalWeight * mean`, closing the
  outside-payoff algebra by construction for that normalized affine source
  model.  The report-required mapped-actor paper-interface endpoint now also
  has a full-support specialization, replacing the two displayed selected-test
  positive-mass assumptions by full support of the finite test law.  The
  optional-reporting mapped-actor paper-interface endpoint now has the matching
  finite-test full-support route: a concrete finite test law is pushed forward
  to reported scores, and full support of the finite law supplies the selected
  score-mass facts.  Both optional-reporting and report-required strongest
  mapped-actor routes now also have existential distinct-test wrappers, matching
  Definition 5's paper-facing relevance-witness language.  A stricter
  skill-dependent conditional-kernel route remains optional
  if the final source-facing statement needs true conditional-on-skill laws.
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
   it separate from Gaussian calculus.  The current closed seam reaches
   support-at-mean and no-distinct-positive-mass actor values under observable
   fairness plus two-sided best response, and now derives observable fairness
   implies test-blankness from either a final off-mean positive-mass acting
   witness or the stronger two-distinct-positive-mass-values witness.  The
   source-shaped witness structures are the current non-certificate endpoints.
   The point-estimate constructors now close the off-mean field for deterministic
   scalar estimate surfaces, and the direct point-estimate endpoints close the
   observable-to-test-blank bridge once mixture, best-response, and affine-payoff
   identities are supplied.  The optional-reporting and report-required
   point-estimate wrappers now derive the needed two-sided best-response
   predicate directly from the concrete source equilibrium models.  The
   PMF binary-mixture wrapper discharges the positive-share mixture identity
   when observable-access estimates are built from `lg21BinaryMixturePMF`, and
   the optional-reporting and report-required endpoints now combine this with
   concrete Definition 1 best response.  The base-indexed optional-reporting
   affine endpoint now makes the paper's reported-score and no-report payoff
   formulas definitional, and the concrete binary-mixture point-estimate
  surface removes the remaining surface identity hypotheses.  The concrete
  fairness endpoint adds the latent-to-observable mixture reduction, and the
  `_self_law` wrapper removes the redundant finite PMF-to-law bridge.  The
  logical bridge
  `paper_theorem3_2_fairness_implies_test_blank_of_not_latent_or_observable_fair`
  converts the stronger continuous no-fairness endpoints into the paper's
  implication shape.  The
  base-indexed report-required affine endpoint now makes the taking payoff
   formula definitional, and the concrete report-required fairness endpoint
   adds the corresponding binary-mixture surface and latent-to-observable
   reduction.  The centered-outside variant reduces the report-required
   outside payoff to a numerator-equals-half-denominator identity.  The
   point-estimate unfairness wrapper now turns these implications into direct
   unfairness from an off-mean point-estimate witness, with a concrete
   optional-reporting direct endpoint already routed through the optional
   binary-mixture surface and a report-required direct endpoint routed through
   the centered outside-payoff variant.  The distinct-tests bridge now replaces
   the off-mean witness with the paper-facing condition that two full-feature
   point estimates at one base profile differ, and the concrete optional and
   report-required wrappers now state that condition directly.  The localized
   supported-test wrappers additionally avoid the global all-tests support
   premise by requiring positive actor mass only for the two displayed tests.
   Finite event-share helpers now package reporter/taker shares as `NNReal`
   values and prove the `≤ 1` and strict-positivity obligations from
   `pmfProb` facts; the event-share concrete endpoints now use those shares
   directly.  The report-required centered base-term endpoint makes the
   outside-payoff algebra a source-formula identity rather than a centered
   numerator equality.  The constant-latent event-share endpoints remove the
   abstract latent-to-observable mixture assumptions for the corresponding
   concrete surfaces, and the mapped-actor-law variants reduce the displayed
   support facts to positive mass of the displayed concrete test/skill values.
   The centered-base-term-by-definition variant closes the report-required
   outside-payoff algebra for the normalized affine source model.  The optional
   posterior-payoff and report-required unit-centered continuous routes now
   also have concrete no-relevance wrappers, so their fairness hypotheses rule
   out every base/test witness directly rather than only through the abstract
   test-blank predicate.  The optional posterior-payoff route also has
   `_of_nonempty_equilibrium` wrappers that choose the positive-share
   contradiction witness internally from nonempty equilibrium/base spaces; the
   report-required unit-centered route now has the same nonempty-equilibrium
   cleanup.  The compact certificate-level event-share source-equilibrium
   endpoints also now choose the equilibrium/base contradiction witness
   internally and expose implication/no-relevance wrappers, reducing the final
   source-facing route to certificate, positive-share, mixture-definition, and
   payoff-normalization data while preserving Theorem 3.2's exact conclusion
   shape.  They also now build the compact
   `LG21FairnessImpossibilityCertificate` consumed by the top-level paper
   interface theorem.  The event-share source-equilibrium route now also has
   optional-reporting and report-required event-or-blank wrappers, plus Section
   3 hidden-access versions, so the route follows the paper proof's split
   between positive reporter/taker share and already-test-blank profiles rather
   than assuming a global positive share.  The share-language bridge
   `paper_interface_theorem3_2_pmf_event_share_fn_pos_iff_exists_pos_mass`
   proves that positive finite share is equivalent to a positive-mass event
   atom, and
   `paper_interface_theorem3_2_positive_event_or_blank_of_zero_event_share_blank`
   converts a zero-share-implies-blank premise into the event-or-blank split.
   `paper_interface_theorem3_2_no_positive_event_blank_of_zero_event_share_blank`
   gives the direct premise conversion needed by the compact Section 3
   wrappers.  The corresponding zero-share Section 3 wrappers
   `paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility_of_zero_event_share_blank`,
   `paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance_of_zero_event_share_blank`,
   `paper_interface_theorem3_2_section3_report_required_fairness_impossibility_of_zero_event_share_blank`,
   and
   `paper_interface_theorem3_2_section3_report_required_no_test_relevance_of_zero_event_share_blank`
   expose the final implication/no-relevance forms with that paper-style
   premise.  The constructor
   `paper_interface_theorem3_2_full_feature_estimate_blank_on_zero_event_share`
   and its case-split wrapper
   `paper_interface_theorem3_2_positive_event_or_blank_of_blank_on_zero_event_share`
   discharge this branch by construction for surfaces that explicitly blank
   full-feature estimates when the finite event share is zero.  The
   optional/report-required wrappers
   `paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility_of_blank_on_zero_event_share`
   and
   `paper_interface_theorem3_2_section3_report_required_fairness_impossibility_of_blank_on_zero_event_share`
   route the final fairness-implies-test-blankness statements through that
   constructor.  The no-relevance counterparts
   `paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance_of_blank_on_zero_event_share`
   and
   `paper_interface_theorem3_2_section3_report_required_no_test_relevance_of_blank_on_zero_event_share`
   route the contrapositive statements through the same constructed surface.
   The raw no-relevance variants
   `paper_interface_theorem3_2_section3_optional_reporting_no_raw_relevance_on_nonzero_share_of_blank_on_zero_event_share`
   and
   `paper_interface_theorem3_2_section3_report_required_no_raw_relevance_on_nonzero_share_of_blank_on_zero_event_share`
   combine those endpoints with the raw-preservation lemma, so the
   conclusion is stated for the unnormalized raw full-feature law on nonzero
   reporter/taker-share profiles.  The positive-event variants
   `paper_interface_theorem3_2_section3_optional_reporting_no_raw_relevance_on_positive_event_of_blank_on_zero_event_share`
   and
   `paper_interface_theorem3_2_section3_report_required_no_raw_relevance_on_positive_event_of_blank_on_zero_event_share`
   state the same conclusion directly for positive-mass reporter/taker atoms.
   The compact certificate aliases
   `paper_interface_theorem3_2_optional_reporting_fairness_impossibility_certificate_of_gaussian_upper_tail_event_or_blank_source_equilibrium`,
   `paper_interface_theorem3_2_optional_reporting_fairness_impossibility_certificate_of_gaussian_upper_tail_zero_event_share_blank_source_equilibrium`,
   `paper_interface_theorem3_2_report_required_fairness_impossibility_certificate_of_upper_tail_event_or_blank_source_equilibrium`,
   `paper_interface_theorem3_2_report_required_fairness_impossibility_certificate_of_upper_tail_zero_event_share_blank_source_equilibrium`,
   `paper_interface_theorem3_2_optional_reporting_fairness_impossibility_certificate_of_gaussian_upper_tail_event_or_blank_constant_latent_surface_posterior_payoff`,
   `paper_interface_theorem3_2_optional_reporting_fairness_impossibility_certificate_of_gaussian_upper_tail_blank_on_zero_event_share_constant_latent_surface_posterior_payoff`,
   `paper_interface_theorem3_2_report_required_fairness_impossibility_certificate_of_upper_tail_event_or_blank_constant_latent_surface_unit_centered_payoff`,
   and
   `paper_interface_theorem3_2_report_required_fairness_impossibility_certificate_of_upper_tail_blank_on_zero_event_share_constant_latent_surface_unit_centered_payoff`
   package the source-equilibrium event-or-blank, source zero-share, concrete
   event-or-blank, and constructed blank-on-zero-share routes as
   `LG21FairnessImpossibilityCertificate`s.
   The source-equilibrium event-or-blank and zero-share certificate routes now
   also expose direct Section 3 implication/no-relevance aliases:
   `paper_interface_theorem3_2_section3_optional_reporting_fairness_implies_test_blank_of_gaussian_upper_tail_zero_event_share_blank_source_equilibrium`,
   `paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance_of_gaussian_upper_tail_event_or_blank_source_equilibrium`,
   `paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance_of_gaussian_upper_tail_zero_event_share_blank_source_equilibrium`,
   `paper_interface_theorem3_2_section3_report_required_fairness_implies_test_blank_of_upper_tail_zero_event_share_blank_source_equilibrium`,
   `paper_interface_theorem3_2_section3_report_required_no_test_relevance_of_upper_tail_event_or_blank_source_equilibrium`,
   and
   `paper_interface_theorem3_2_section3_report_required_no_test_relevance_of_upper_tail_zero_event_share_blank_source_equilibrium`.
   The fully concrete optional
   posterior-payoff and report-required unit-centered constant-latent
   event-share endpoints now also have direct Section 3 hidden-access wrappers,
   and short `PaperInterface` aliases
   `paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility`
   and
   `paper_interface_theorem3_2_section3_report_required_fairness_impossibility`
   are the final implication audit targets.  The matching short no-relevance
   aliases
   `paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance`
   and
   `paper_interface_theorem3_2_section3_report_required_no_test_relevance`
   expose the contrapositive paper reading directly from the same case-split
   concrete surfaces.  This finite
   binary-mixture route remains available if the final statement wants those
   exact point-mass endpoints; its remaining obligations are the displayed
   positive-mass/support facts.  The active continuous/source route should now
   only need a stricter conditional-kernel version if the final statement is
   intentionally broadened beyond the concrete constant-latent event-share
   surfaces used by the current Section 3 wrappers.

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
