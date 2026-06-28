# Final Validation Report: Quantifying Spatial Under-reporting Disparities

This is a partial validation report, not a completion certificate. The paper is
partially formalized and ready to be presented as a public partial checkpoint.

Status checkpoint: 2026-06-28, after tightening the finite observed-window and
local stopping-certificate proof campaign to a compact primitive-wrapper
boundary. The checked Theorem 1 / Appendix Theorem 2 route now starts from
`Theorem2PrimitiveSourceModel`, which packages a homogeneous Poisson count law
with fixed paper `g(s)` and `h_m(e)` kernels, proves the zero/one/multi
observed-window factorizations, and constructs finite independent Poisson
count-family witnesses whose product likelihood collapses to one total-count
PMF. The Eq. (33)/(34) min-censored preprocessing windows now have checked
stopping-time closure under explicit endpoint stopping-time premises, fixed
endpoint specializations, and first-count-arrival certificates whose level sets
are adapted count-threshold events. The local finite-observation certificate
now packages count observability, first-count level sets, endpoint stopping
facts, and duration censoring into one library-level stopping-window theorem.
The same local certificate route now also has stochastic-endpoint
paper-facing rows and pathwise deterministic `ObservationWindow` projections
from the certified stopping windows. The realized stopping-window bridge now
also feeds the Appendix B.2 zero/one/multi source-data factorization rows, and
the NYC/Chicago local-count preprocessing rows include zero/one/multi-report
factorization over the certified pathwise exposure.
Proving or supplying the compact process/stopping/kernel certificate bundle
remains the next closure target: the homogeneous counting-process law, fixed
Condition 1/2 kernels, and local stopping-certificate fields for the concrete
process/endpoints. Under the standard homogeneous Poisson process model this is
expected to be true, but shrinking it further requires deeper
continuous-time/natural-filtration library work.

## 1. Human Verdict

- Lean formalization status: partially formalized
- Human dashboard review status: current closeout surface has 87 unreviewed
  items: 84 paper-interface rows plus 3 explicit assumption rows. The
  statement, assumption, review-surface, and source-record sidecars are current
  for this public partial checkpoint.
- Paper correctness verdict: theorem target selected; one appendix proof-formula
  typo identified in the `M > 1` residual factor
- Qualitative proof verdict: source-facing Poisson, interarrival-kernel,
  min-censored preprocessing-window, MLE, regression, and zero-inflation algebra
  is Lean-checked; the full continuous-time source-record construction remains
- Lean footprint: `lake build LBG24SpatialUnderreporting` passes

## 2. Source and Scope

- Paper: *Quantifying Spatial Under-reporting Disparities in Resident Crowdsourcing*
- Authors: Zhi Liu, Uma Bhandaram, Nikhil Garg
- Source version: arXiv `2204.08620` v4, revised 2023-12-06, cross-checked
  against Nature Computational Science supplementary material for Appendix B
- Version of record: Nature Computational Science 4, 57-65 (2024), DOI
  `10.1038/s43588-023-00572-6`
- Lean folder: `papers/LBG24SpatialUnderreporting`
- Human-facing theorem file: `papers/LBG24SpatialUnderreporting/PaperInterface.lean`
- Paper assumption file: `papers/LBG24SpatialUnderreporting/Assumptions.lean`

## 3. What Has Been Proven

- Eq. (2): source Poisson count PMF formula, grounded in mathlib's Poisson
  measure through `EconCSLib.Foundations.Probability.PoissonProcess`.
- Homogeneous at-least-one-report probability:
  `1 - exp (-(reportingRate * duration))`.
- Lemma 1 duration-mixture probability checks: the source-facing
  continuous-duration first-report probability has nonnegativity and upper-bound
  checks under normalized nonnegative density/rate hypotheses, and implementation
  support also proves the finite-support weighted-average analogue.
- Lemma 1 continuous-duration first-report probability: for a normalized
  density over nonnegative incident durations, the homogeneous source expression
  `1 - integral exp(-lambda t) f(t)` equals the integral of the per-duration
  first-report probability, and the continuous observed unique-incident rate is
  the occurrence rate times that integral. The implementation also proves the
  analogous source algebra for nonhomogeneous cumulative intensity
  `integral_0^t lambda(u) du`.
- Lemma 1 continuous-duration Poisson thinning count law: a latent Poisson
  incident count thinned by the continuous-duration detection probability has
  observed-count likelihood with mean equal to the continuous observed incident
  rate. Implementation support also proves the finite-duration and
  nonhomogeneous cumulative-intensity variants. A reusable
  `PoissonThinningCountLaw` certificate packages the latent-Poisson plus
  binomial-thinning mixture and derives the thinned Poisson count mass.
- Lemma 1 unit-interval LLN route: IID, integrable observed unique-incident
  counts have almost-sure time-average limit equal to their one-period mean,
  and hence to the finite-duration observed incident rate when that mean is
  supplied by the stochastic model.
- Homogeneous reporting-delay mean: the expectation integral of a rate-`lambda`
  exponential waiting time is `1 / lambda`.
- Appendix Lemma 2 tail form: after the source proof's sum/integral collapse,
  the shifted Poisson count mass contributes one inside the normalized
  restricted start-density integral over `s >= t1`, yielding the tail
  probability of an exponential waiting-time model with the same positive rate.
- Appendix Lemma 2 memoryless-tail algebra: the ratio
  `noArrivalProb rate (elapsed + future) / noArrivalProb rate elapsed`
  equals the future no-arrival probability.
- Appendix Lemma 2 Poisson-mass step: the total mass of the Poisson count
  likelihood is one for nonnegative rate-exposure product, matching the
  source proof's summation over possible pre-start counts.
- Appendix Lemma 2 density-mixture step: after the memoryless property makes
  the future no-arrival tail independent of the realized start time, integrating
  it against a normalized `g(s)` density, including the restricted `s >= t1`
  version used in the source proof, returns the same no-arrival tail.
- Appendix Lemma 2 process-law consequences: under
  `HomogeneousPoissonProcessLaw`, zero-count windows, ordered one-jump
  densities, and ordered finite-jump densities rewrite to the corresponding
  exponential tail/PDF forms at the shared process rate; one/finite-jump
  ordered-density normalizations are tied to count probabilities through the
  checked ordered-region volume lemmas.
- Proposition 1 homogeneous, continuous-duration, and finite-duration
  non-identifiability cores: for any observed rate, two distinct reporting
  rates with nonzero first-report probabilities can be paired with
  corresponding occurrence rates to produce the same observed unique-incident
  rate; positive-premise variants derive those nonzero probabilities for the
  homogeneous and finite-support cases.
- Appendix B.2 raw algebra: a likelihood case of the form
  `A * rate^M * exp (-(rate * exposure))` factors as a corrected residual times
  the Poisson count PMF.
- Appendix B.2 interarrival collection: one-report and multi-report
  no-arrival/interarrival density kernels collect to the source
  `rate^M * exp (-rate * exposure)` shape.
- Appendix B.2 process-kernel source cases: the zero-report, one-report, and
  multi-report process-kernel likelihoods factor directly into a Poisson count
  PMF and a rate-independent residual.
- Appendix B.2 condition-function/source-data layer: the paper's `g(s)`,
  `h_m(e)`, and survival-integral bookkeeping constructs
  `Theorem2ProcessSourceData` from reusable observation-window no-arrival and
  interarrival kernel certificates before converting to the older
  process-kernel case; the raw one/multi-report rows now expose nonnegative
  gap/tail and ordered-timeline side conditions.
- Appendix B.2 density-kernel layer: one-report and multi-report source-data
  likelihoods are decomposed into the rate-independent `g`/`h_m`/survival
  residual times the reusable arrival kernel, and also into exponential
  PDF/survival form under nonnegative gap/tail conditions.
- Appendix B.2 process-law layer: zero-report likelihoods are connected to a
  homogeneous count-process law, one/multi-report likelihoods are connected to
  reusable homogeneous arrival-density laws, and all three cases are packaged
  under `HomogeneousPoissonProcessLaw` with one shared rate before the final
  Poisson-PMF factorization.
- Appendix B.2 explicit finite source/density layer:
  `Theorem2ConditionSourceModel` and
  `Theorem2ConditionDensitySourceModel` expose the paper's Condition 1/2
  source kernels, density kernels, survival integrals, and zero/one/multi
  observed-window data directly. The older
  `assumption_theorem2_poisson_process_and_conditions`, formula-facing
  counting-process law, combined process law, and source-data rows remain as
  audit layers below this theorem-facing finite boundary.
- Appendix B.2 observed jump-time accounting: one-report and multi-report
  source data can be built from actual start/end/jump times; Lean proves the
  interarrival gaps plus terminal tail telescope to `end - start`, and
  ordered-window rows derive nonzero exposure from `start < end` and
  nonnegative interarrival gaps and terminal tails from the jump-time ordering
  premises.
- Eq. (33)/(34) preprocessing stopping-window closure: under explicit
  endpoint stopping-time premises, fixed inspection/work-order or
  closure/retrieval endpoints, a first-count-arrival certificate, or the
  single local finite-observation certificate, the 100-day min-censored
  preprocessing rules construct `StoppingObservationWindow` records with
  nonnegative exposure. The local-count-process route now also covers
  stochastic endpoint rules directly and projects each realized stopping
  window to the deterministic `ObservationWindow` object used downstream.
  Zero/one/multi-report source-data factorization over the certified pathwise
  NYC/Chicago exposure is checked.
- Stopping-window to Appendix B.2 finite layer: for any realized
  `StoppingObservationWindow`, Lean proves the zero-, one-, and multi-report
  source-data factorizations over the deterministic pathwise window, with
  one/multi rows requiring the explicit observed-jump ordering premises.
- Theorem 1 / Appendix Theorem 2 conditional statement from explicit finite
  `Theorem2ConditionSourceModel` and
  `Theorem2ConditionDensitySourceModel` records, with observed zero/one/multi
  window data; the legacy source-assumption, process-law, source-data, and
  kernel rows remain as audit layers showing the no-arrival/interarrival
  collection and corrected Poisson count-likelihood residual from
  source-shaped cases.
- Finite-product Theorem 1 form: a finite product of validated condition
  source/density observed-window records constructs finite independent Poisson
  count-family witnesses and collapses to one total-count Poisson PMF with a
  rate-independent residual.
- Eq. (3): finite products of incident Poisson likelihood factors collapse to
  `rate^(sum counts) * exp(-rate * sum exposure)` up to a rate-independent
  residual, and also to one total-count Poisson PMF.
- Eq. (3): the displayed MLE ratio solves the Poisson score equation and
  globally maximizes the rate-dependent Poisson log-likelihood kernel over
  positive rates under positive exposure and nonzero total count.
- Eq. (5)-(6): exact log-link rate formula, log-link positivity, and Poisson
  regression likelihood specialization.
- Eq. (7): generic and regression-rate-substituted zero-inflated likelihood
  case splits, plus nonnegativity under `0 <= gamma <= 1` and nonnegative mean.

## 4. Paper Assumption Provenance

Paper-local source assumptions currently exported from `Assumptions.lean` and
listed in `status.json` `review_surface.assumption_names` include
`theorem2_poisson_process_and_condition_semantics`,
`Theorem2PrimitiveSourceModel`, and
`assumption_theorem2_poisson_process_and_conditions`.

`Theorem2PrimitiveSourceModel` is now the preferred theorem-facing wrapper: it
bundles `HomogeneousPoissonCountingProcessByLaw` with fixed paper Condition
1/2 kernels, and Lean derives the rate-indexed density-source model with
rate-independence by reflexivity. The older
`assumption_theorem2_poisson_process_and_conditions` remains a process-source
audit layer bundling the reusable count law with `Theorem2ConditionFunctions`.
Lower-level `Theorem2ConditionSourceModel` and
`Theorem2ConditionDensitySourceModel` routes are retained as audit/support
layers. Before the paper can be called fully formalized without a conditional
boundary, the homogeneous count law, fixed Condition 1/2 kernels, and local
stopping-certificate fields for the concrete process/endpoints must be derived
from process primitives and Conditions 1/2, or independently validated as an
intentional source-assumption bundle by the assumption/provenance workflow.

The last generated code-backed recursive source-record audit
`source_record_audit.json` expands the configured review surface into
86 field-level items, including
`Theorem2ConditionFunctions`, `HomogeneousPoissonCountingProcessByLaw`, the
derived formula-facing counting-process/count-law interfaces, and
`HomogeneousPoissonProcessLaw`. The recursive audit has zero recursion
failures and digest
`206a009577f8d298da44da7c8327e2b88fa64ffa6232c21cc9cbb46fb5e02900`.
The matching `source_record_match_llm.json` provenance sidecar is present and
current for the public partial checkpoint. It classifies audited containers,
source-model data, and approved external-boundary leaves; it does not turn the
remaining stopping-certificate boundary into a completed theorem.

## 5. Additional Assumptions Beyond Paper

- None added as hidden assumptions.
- Visible theorem side conditions include nonzero first-report probabilities,
  nonzero exposure, positive reporting rate for exponential waiting-time
  statements, positive total exposure/nonzero total count for global MLE, and
  zero-inflation parameter bounds. These are ordinary mathematical domain
  conditions, not hidden paper assumptions.

## 6. Proof-Strategy Deviations

- Continuous source expressions such as `P(S=t | ...)`, `P(E=t | ...)`, and
  `P(T_j=t_j | ...)` are treated as density/likelihood-kernel factors rather
  than literal point probabilities.
- Appendix B.2's printed `M > 1` residual appears inverted relative to the
  displayed Poisson PMF. The Lean theorem proves the corrected factor
  `M! / exposure^M` in the residual.
- Proposition 1 now has homogeneous and finite-duration collision theorems,
  positive-premise variants, and an IID unit-interval LLN route. The remaining
  stochastic work is deriving the IID/integrability and one-period-mean
  premises from a thinning/steady-state Poisson model.

## 7. Proof Tricks Worth Reusing

- `EconCSLib.Foundations.Probability.PoissonProcess` now provides reusable
  Poisson count-likelihood, no-arrival, interarrival-density, jump-time
  telescoping, ordered-timeline gap/tail nonnegativity, finite-product,
  zero-inflated, nonnegativity, source-kernel certificate, Poisson-binomial
  thinning algebra, and MLE kernel algebra.
- `interarrivalTailLikelihood_eq_exposure_rawShape` is the reusable collection
  step for products of homogeneous Poisson interarrival densities plus a
  terminal no-arrival tail.
- `interarrivalDensityKernel_eq_exponential_pdfReal`,
  `OneInterarrivalTailKernel.likelihood_eq_exponential_pdfReal_mul_tail`, and
  `FinInterarrivalTailKernel.likelihood_eq_exponential_pdfReal_prod_mul_tail`
  connect the interarrival kernels to exponential PDF/survival formulas once
  nonnegative gaps and tails are available.
- The ordered-window specializations
  `OneInterarrivalTailKernel.fromOrderedWindow_likelihood_eq_exponential_pdfReal_mul_tail`
  and
  `FinInterarrivalTailKernel.fromOrderedTimeline_likelihood_eq_exponential_pdfReal_prod_mul_tail`
  package those nonnegativity proofs for observed ordered timelines.
- `ratePowerExp_factor_countLikelihood` is the reusable bridge from
  arrival-time density algebra to Poisson count-likelihood factorization.
- `Theorem2ProcessKernelCase` is the paper-local explicit source-kernel
  implementation bridge, and `Theorem2ProcessSourceData` is the narrower
  source-data audit layer below the theorem-facing source assumption.
- `HomogeneousArrivalDensityLaw` and `HomogeneousPoissonProcessLaw` are the new
  reusable boundary interfaces for ordered jump-time densities plus interval
  count laws with a shared Poisson rate.
- `Theorem2ProcessLawCase` is the paper-local audit point for applying that
  combined process law uniformly across the zero/one/multi Appendix B.2 cases,
  below `Theorem2ObservedWindowCase` and
  `assumption_theorem2_poisson_process_and_conditions`.
- `poissonRateLogLikelihoodKernel_le_at_mle` proves the reusable global
  positive-rate Poisson log-likelihood kernel maximizer.

## 8. Library Lift Pass

Completed:

- Added `EconCSLib/Foundations/Probability/PoissonProcess.lean`.
- Imported it from `EconCSLib/Foundations/Probability.lean`.
- Added finite-product Poisson likelihood algebra for total count/total
  exposure calculations.
- Added interarrival-density and no-arrival tail collection lemmas for
  finite-dimensional Poisson process likelihood calculations.
- Added paper-neutral `NoArrivalKernel`, `OneInterarrivalTailKernel`, and
  `FinInterarrivalTailKernel` certificates, plus nonnegativity lemmas.
- Added paper-neutral jump-time endpoint/gap/tail helpers and a telescoping
  exposure theorem for observed interarrival times.
- Added paper-neutral ordered-timeline nonnegativity helpers and reusable
  `OrderedOneJumpWindow`, `OrderedFiniteJumpTimeline`,
  `OneInterarrivalTailKernel.fromOrderedWindow`, and
  `FinInterarrivalTailKernel.fromWindowJumpTimes` constructors, plus strict
  observation-window exposure.
- Added `NoArrivalKernel.fromWindow` and its count-process-law bridge
  `HomogeneousCountProcessLaw.windowNoArrivalKernel_likelihood_eq_prob` for
  zero-report windows.
- Added `noArrivalProb_add_div_noArrivalProb_left` and the paper-local
  `lemma2_no_arrival_memoryless_tail_ratio` support theorem for Lemma 2's
  residual waiting-time argument.
- Added `tsum_countLikelihood` and the paper-local
  `lemma2_poisson_count_likelihood_tsum_one` support theorem for Lemma 2's
  Poisson count-PMF mass-one summation step.
- Added generic and restricted-start no-arrival density-mixture theorems,
  plus the paper-local `lemma2_no_arrival_density_mixture_on_Ici` and
  `lemma2_no_arrival_density_mixture_with_poisson_count_mass_on_Ici` support
  theorems for Lemma 2's Eq. (14)-to-Eq. (16) normalized-density/count-mass
  collapse.
- Added exponential PDF/survival bridges for one-report and multi-report
  interarrival-tail kernels under nonnegative gap/tail side conditions.
- Added paper-local source-data density decomposition lemmas before the final
  Poisson-PMF collection step.
- Added reusable `HomogeneousArrivalDensityLaw` and
  `HomogeneousPoissonProcessLaw` interfaces, plus paper-local zero/one/multi
  process-law factorization theorems that route Appendix B.2 through one shared
  homogeneous process rate.
- Added reusable `ArrivalKernelCase` and a combined-process-law
  `observedArrivalCaseLikelihood` bridge, so LBG source-data and process-law
  cases expose the generic no/one/finite arrival kernel before Poisson-PMF
  collection.
- Added the unified paper-local `Theorem2ProcessLawCase` bridge from combined
  process-law cases to `Theorem2ProcessSourceData`.
- Reused the GN21 renewal/LLN strong-law wrapper for the Lemma 1
  unit-interval observed-count route.
- Added finite-duration first-report weighted-average and probability-bound
  lemmas for Lemma 1's duration-mixture layer.
- Added continuous-duration Lemma 1 integral algebra for homogeneous reporting
  rates and the nonhomogeneous cumulative-intensity source formula.
- Added ordered-window one-report and multi-report jump-time factorization
  rows, deriving the nonzero exposure side condition from `start < end` and
  exposing the jump ordering needed for nonnegative gaps and terminal tails.
- Added reusable Poisson-binomial thinning algebra: a real binomial thinning
  mass, reindexed summand identity, discarded-arrival `HasSum`/`tsum`
  identities, and the full unshifted `HasSum`/`tsum` thinning theorem over
  original arrival counts.
- Added reusable `PoissonThinningCountLaw` and the paper-local
  `lemma1FiniteDurationPoissonThinningCountLaw` constructor.
- Added nonnegativity lemmas for binomial thinning masses and Poisson-thinning
  summands under `0 <= p <= 1`.
- Added the paper-facing continuous-duration Poisson thinning count law by
  applying the reusable thinning theorem to the Lemma 1 source detection
  probability; finite-duration and nonhomogeneous cumulative-intensity variants
  remain as implementation support.

Deferred reusable candidates:

- Full homogeneous Poisson process construction with independent increments,
  interarrival densities, first-jump splitting, stopping-window likelihood
  kernels, and conditional density semantics proving
  `HomogeneousPoissonProcessLaw` from primitive process definitions.
- Steady-state justification for deriving the Lemma 1 IID unit-interval mean
  premises from a primitive incident model. The Poisson-binomial thinning
  algebra itself is now checked.

## 9. Conditional Results and Remaining Gaps

Primary gap:

- Prove the source assumption bundle
  `assumption_theorem2_poisson_process_and_conditions` from primitive
  continuous-time Poisson-process/stopping-window semantics and the paper's
  Conditions 1/2, instead of taking that bundle as a visible construction
  boundary. The zero-report no-arrival kernel is tied directly to
  `HomogeneousCountProcessLaw`, and the one/multi interarrival kernels are
  connected to exponential PDF/survival formulas; what remains is the
  stochastic process theorem producing the shared process law and condition
  functions from the paper's conditional process semantics.

Secondary gap:

- Derive the Lemma 1 IID unit-interval count law and one-period mean from a
  primitive Poisson thinning/steady-state model.

## 10. Suspected Paper Errors or Inconsistencies

Appendix B.2, `M > 1` case:

- Eq. (31) isolates `lambda^M exp(-lambda(e-s))` times a rate-independent
  kernel factor.
- The displayed Poisson PMF includes `(lambda(e-s))^M / M!`.
- Therefore the residual needed for Eq. (32) is the kernel factor times
  `M! / (e-s)^M`.
- The source text and Nature supplementary material print `(e-s)^M / M!`
  instead. The main theorem remains correct because it only requires the
  existence of a rate-independent residual.

## 11. Validation Checks

Run so far:

```bash
lake build EconCSLib.Foundations.Probability.PoissonProcess
lake build LBG24SpatialUnderreporting
python3 -m json.tool papers/LBG24SpatialUnderreporting/status.json
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper LBG24SpatialUnderreporting --out papers/LBG24SpatialUnderreporting/source_record_audit.json
python3 scripts/review_dashboard.py --paper LBG24SpatialUnderreporting --statement-precheck
python3 scripts/review_dashboard.py --paper LBG24SpatialUnderreporting --assumption-precheck
python3 scripts/audit_repository.py --paper LBG24SpatialUnderreporting --paper-closeout --include-active --info-limit 0
```

Closeout results:

- Lean build passes.
- The recursive source-record audit has zero recursion failures.
- Statement precheck is current for 84 paper-interface rows, with 84
  Lean-to-TeX drafts, 84 statement-judge rows, and 56 strict mismatches
  accepted as conditional boundaries.
- Assumption precheck is current for 3 assumption declarations, with no
  missing, stale, or flagged items.
- `review_surface_llm.json`, `assumption_match_llm.json`,
  `statement_match_llm.json`, and `source_record_match_llm.json` are populated
  for the expanded public partial review surface.
- Repository paper-closeout audit exits successfully for the public partial
  checkpoint. Broad theorem wrappers are retained as auxiliary proof-facing
  rows outside the reviewed public surface, and the remaining stopping
  certificate premise shapes are documented caveats rather than hidden
  assumptions.
- `DependencyDAG.tex` and `DependencyDAG.pdf` are present as a human-facing
  roadmap with paper-facing node text rather than Lean declaration names.
- `python3 scripts/sync_paper_status.py` completes without the earlier timeout;
  aggregate generated status files have been refreshed from the paper-local
  `status.json`.

## 12. Final Verdict

Completion status: partially formalized.

The algebraic theorem core is checked in Lean and the finite source/density
surface is explicit as an audit layer. The preferred public route is now the
compact `Theorem2PrimitiveSourceModel` plus
`DurationCensoredFirstCountObservationCertificate` boundary. The Eq. (33)/(34)
min-censoring stopping-window bookkeeping is checked from endpoint
stopping-time premises, fixed endpoint specializations, and first-count-arrival
certificates. The paper is not yet fully formalized because the concrete
continuous-time process theorem has not been used to supply the homogeneous
count-process law, fixed `g`/`h_m` kernels, and local stopping-certificate
fields for the actual process/endpoints.

## 13. Named Theorem Statements Checked

- `equation2_poisson_count_pmf_formula`
- `first_report_probability_formula`
- `lemma1_continuous_duration_first_report_probability_integral`
- `lemma1_continuous_duration_observed_rate_integral`
- `lemma1_finite_duration_first_report_weighted_average`
- `lemma1_continuous_duration_first_report_probability_nonnegative`
- `lemma1_continuous_duration_first_report_probability_le_one`
- `lemma1_unit_interval_observed_counts_lln`
- `lemma1_unit_interval_observed_counts_lln_to_continuous_duration_rate`
- `lemma1_continuous_duration_poisson_thinning_count_law`
- `lemma2_exponential_waiting_tail`
- `homogeneous_reporting_delay_mean_formula`
- `equation3_mle_score_equation`
- `equation3_mle_global_logLikelihood_max`
- `equation3_product_likelihood_raw_shape`
- `equation3_product_likelihood_total_pmf`
- `equation5_poisson_regression_rate_formula`
- `equation6_poisson_regression_likelihood_formula`
- `equation7_zero_inflated_likelihood_zero`
- `equation7_zero_inflated_likelihood_positive_count`
- `equation7_zero_inflated_regression_likelihood_zero`
- `equation7_zero_inflated_regression_likelihood_positive_count`
- `proposition1_homogeneous_nonidentifiability`
- `proposition1_continuous_duration_nonidentifiability`
- `proposition1_homogeneous_nonidentifiability_positive`
- `proposition1_finite_duration_nonidentifiability_positive`
- `theorem1_likelihood_decomposition`
- `theorem1_likelihood_decomposition_from_primitive_source_model`
- `theorem2_observed_window_source_data_factorization_from_primitive_source_model`
- `theorem2_duration_censored_certificate_source_data_factorization_from_primitive_source_model`
- `theorem2_zero_report_duration_censored_certificate_source_data_factorization_from_primitive_source_model`
- `theorem1_likelihood_decomposition_from_process_source_data`
- `theorem2_zero_report_condition_functions_factorization`
- `theorem2_one_report_condition_functions_factorization`
- `theorem2_one_report_jump_time_factorization`
- `theorem2_multi_report_condition_functions_factorization`
- `theorem2_multi_report_jump_times_factorization`
- `theorem2_one_report_proper_window_factorization_row`
- `theorem2_multi_report_proper_window_factorization_row`
- `theorem1_likelihood_product_decomposition_from_primitive_source_model_of_exists_pos_exposure`
- `theorem1_source_data_product_decomposition_from_primitive_source_model_of_exists_pos_exposure`
- `theorem1_exists_finite_poisson_count_family_for_primitive_source_model_total_count_event_of_exists_pos_exposure`
- `theorem1_likelihood_product_decomposition_from_process_law_cases`
- `theorem1_likelihood_product_decomposition_from_process_source_data`
- `theorem2_zero_report_source_case`
- `theorem2_one_report_source_case`
- `theorem2_multi_report_source_case`
- `theorem2_interarrival_kernel_collection`
- `theorem2_one_report_kernel_collection`
- `theorem2_multi_report_kernel_collection`
- `theorem2_zero_report_process_kernel_source_case`
- `theorem2_one_report_process_kernel_source_case`
- `theorem2_multi_report_process_kernel_source_case`
- `theorem2_corrected_case_factorization`
- `equation7_zero_inflated_likelihood_nonnegative`

## 14. Paper-Facing Statement Validator Ledger

Statement validator sidecars are populated for this checkpoint. Recheck them
with:

```bash
python3 scripts/review_dashboard.py --paper LBG24SpatialUnderreporting --precheck
```
