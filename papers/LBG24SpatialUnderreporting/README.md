# Quantifying Spatial Under-reporting Disparities in Resident Crowdsourcing

## Source Version

- Paper: *Quantifying Spatial Under-reporting Disparities in Resident Crowdsourcing*
- Authors: Zhi Liu, Uma Bhandaram, Nikhil Garg
- Version formalized: Nature Computational Science 4, 57-65 (2024), version of
  record published 2023-12-05, DOI `10.1038/s43588-023-00572-6`
- Official URL: https://www.nature.com/articles/s43588-023-00572-6
- Open source version: arXiv `2204.08620` v4, revised 2023-12-06
- Public PDF: https://arxiv.org/pdf/2204.08620

The main source PDF is cached locally as ignored `source.pdf`; the working text
cache is ignored `source.txt`, extracted with `mutool`. The Nature supplementary
PDF is cached as ignored `nature_supplementary.pdf` with text cache
`nature_supplementary.txt`.

## Current Status

Status: partially formalized.

Checkpoint: 2026-06-28, after tightening the finite observed-window and local
stopping-certificate proof campaign to a compact primitive-wrapper boundary.
This is ready as a public partial formalization checkpoint: the current
paper-level Lean target builds, the review surface is current for this
checkpoint, and the remaining headline obstruction is isolated. The missing
library theorem is the reusable construction/supply of one fieldful
certificate bundle: the homogeneous Poisson counting-process law, the
duration-censored stopping-certificate fields for the concrete endpoints, and
the fixed paper Condition 1/2 kernels.
The deterministic and stochastic min-censoring bookkeeping for the empirical
Eq. (33)/(34) preprocessing windows is now checked. Lean proves the generic
endpoint-stopping form, the deterministic-endpoint specialization, and a
first-count-arrival route in which the first report is a stopping time because
its level sets match adapted count-threshold events. The reusable
`DurationCensoredFirstCountObservationCertificate` now packages the local
count observability, first-count level-set identity, endpoint stopping facts,
and duration-censoring rule into a single library-level stopping-window
theorem. The same certificate boundary now also has stochastic-endpoint
paper-facing rows and a pathwise projection from each stopping observation
window to the deterministic `ObservationWindow` consumed by the finite
likelihood layer. Zero/one/multi-report source-data factorization over the
certified pathwise NYC/Chicago preprocessing exposure is also checked.
On the Condition 1/2 side, fixed paper `g(s)` and `h_m(e)` data now construct
the rate-indexed density-source model inside Lean, with rate-independence
proved by reflexivity. The preferred public interface exposes this as
`Theorem2PrimitiveSourceModel`; downstream Theorem 1 / Appendix Theorem 2 rows
derive the source-data factorization, product likelihoods, and finite Poisson
count-family witnesses from that wrapper.

The reusable module `EconCSLib.Foundations.Probability.PoissonProcess` now
contains Poisson count-likelihood, no-arrival, interarrival-density, finite
product, zero-inflated likelihood, jump-time telescoping, nonnegativity,
ordered-timeline gap/tail nonnegativity, source-kernel certificate, and
factorization algebra useful for this paper and future queueing/OR papers.
It now includes a lightweight continuous-time `IsStoppingTime` predicate and
`StoppingObservationWindow` constructors proving closure under deterministic
times, nonnegative deterministic shifts, and min-censored endpoint rules.
It also now includes reusable ordered one-jump/window and finite-jump timeline
constructors, Poisson-binomial thinning mass, summand identities, full
`HasSum`/`tsum` thinning theorem, and paper-facing finite-duration thinning
count law needed for the Lemma 1 stochastic-model closure. A reusable
`PoissonThinningCountLaw` certificate now packages the latent-Poisson plus
binomial-thinning mixture and proves the observed thinned count PMF. The current
Appendix B.2 process boundary is narrowed to reusable
`HomogeneousPoissonCountingProcessByLaw` semantics: a count path, zero-start
field, monotone-path field, mathlib independent-increment property, and
stationary Poisson increment laws. From that object the library derives the
formula-facing `HomogeneousPoissonCountingProcess`, `HomogeneousCountProcessLaw`,
finite-dimensional adjacent interval-count product laws, and the canonical
exponential ordered-arrival density law used by `HomogeneousPoissonProcessLaw`;
the Poisson PMF and arrival-density formulas are no longer assumed as opaque
fields. The paper layer now also exposes direct primitive-wrapper routes
through `Theorem2PrimitiveSourceModel`, plus lower-level finite observed-window
routes through `Theorem2ConditionSourceModel` and
`Theorem2ConditionDensitySourceModel`, with zero/one/multi-report source-data
constructors and finite-product total-PMF wrappers. The older
`assumption_theorem2_poisson_process_and_conditions` route remains as a visible
process-source audit layer.
The current recursive source-record audit expands the review surface to 86
field-level items with zero recursion failures. The matching
`source_record_match_llm.json` sidecar is present for this public partial
checkpoint and classifies the remaining process/stopping/kernel leaves as the
approved boundary, not as hidden completed proof obligations.

Proof strategy: the current formalization follows a public partial route with
one explicit source-model boundary. The preferred paper-facing theorems consume
`Theorem2PrimitiveSourceModel`, which is built from a homogeneous count law and
fixed Condition 1/2 kernels; the stopping-window rows consume the separate
`DurationCensoredFirstCountObservationCertificate`. Lean then proves the
zero/one/multi-report Appendix B.2 factorizations, displayed likelihood,
product likelihoods, finite independent Poisson count-family witnesses,
total-count PMF collapse, MLE, and zero-inflated algebra downstream of those
objects. Making the certificate smaller would require a deeper continuous-time
process/natural-filtration theorem that derives its fields automatically. That
construction is future library work and is the reason this artifact is partial.

The current Lean target builds:

```bash
lake build LBG24SpatialUnderreporting
```

## Paper-Facing Ledger

| Paper item | Lean declaration | Status | Remaining assumptions / notes |
|---|---|---|---|
| Eq. (2), Poisson count PMF | `equation2_poisson_count_pmf_formula` | formalized | None. Grounded in mathlib `poissonMeasure` through the reusable wrapper. |
| At-least-one-report probability | `first_report_probability_formula` | formalized | None. Homogeneous no-arrival algebra. |
| Lemma 1 continuous-duration first-report probability and observed rate | `lemma1_continuous_duration_first_report_probability_integral`, `lemma1_continuous_duration_observed_rate_integral` | formalized | None. Homogeneous source integral over nonnegative incident durations: normalized density turns `1 - integral exp(-lambda t) f(t)` into the integral of the per-duration first-report probability, and the observed unique-incident rate is the occurrence rate times that integral. Implementation support also proves the analogous cumulative-intensity version for nonhomogeneous reporting rates. |
| Lemma 1 duration-mixture probability bounds | `lemma1_finite_duration_first_report_weighted_average`, `lemma1_continuous_duration_first_report_probability_nonnegative`, `lemma1_continuous_duration_first_report_probability_le_one` | formalized | None. The source-facing continuous-duration probability is bounded between zero and one under nonnegative density/rate hypotheses; implementation support also proves the finite-support weighted-average analogue and its finite probability bounds. |
| Lemma 1 continuous-duration Poisson thinning count law | `lemma1_continuous_duration_poisson_thinning_count_law` | formalized | None. Collapses a latent Poisson incident count thinned by the continuous-duration detection probability to the observed-count Poisson likelihood with mean equal to the continuous observed incident rate; implementation support also proves finite-duration and cumulative-intensity variants and packages the laws as reusable `PoissonThinningCountLaw` certificates. |
| Lemma 1 unit-interval LLN route | `lemma1_unit_interval_observed_counts_lln`, `lemma1_unit_interval_observed_counts_lln_to_continuous_duration_rate` | formalized | None. Uses the reusable GN21 renewal/LLN strong-law wrapper for IID unit-interval observed counts and targets the continuous-duration observed-rate formula; the stochastic model must still justify IID/integrability and the one-period mean. |
| Appendix Lemma 2 tail form | `lemma2_exponential_waiting_tail` | formalized | None. Source-aligned restricted-start mixture: after the paper's sum/integral collapse, the Poisson count mass contributes one under the normalized `s >= t1` start density and yields the exponential waiting-time tail; implementation support also includes no-arrival memoryless-tail ratio, PMF mass-one, and process-law zero/one/finite-jump exponential tail/PDF consequences. |
| Homogeneous reporting delay mean | `homogeneous_reporting_delay_mean_formula` | formalized | None. Actual expectation integral of a rate-`lambda` exponential clock equals `1 / lambda`. |
| Proposition 1 algebraic non-identifiability | `proposition1_homogeneous_nonidentifiability`, `proposition1_continuous_duration_nonidentifiability`, `proposition1_homogeneous_nonidentifiability_positive`, `proposition1_finite_duration_nonidentifiability_positive` | formalized | None. Exact collision/equal-observed-rate theorems for distinct reporting rates in homogeneous, continuous-duration, and finite-duration-mixture forms; positive-premise variants derive nonzero detection probabilities for the homogeneous and finite-support cases. |
| Theorem 1 / Appendix Theorem 2 likelihood factorization | `theorem1_likelihood_decomposition_from_primitive_source_model`, `theorem2_observed_window_source_data_factorization_from_primitive_source_model`, `theorem2_duration_censored_certificate_source_data_factorization_from_primitive_source_model`, `theorem2_zero_report_duration_censored_certificate_source_data_factorization_from_primitive_source_model` | conditional | The preferred finite route consumes `Theorem2PrimitiveSourceModel`, deriving rate-indexed Condition 1/2 semantics from fixed `g(s)` and `h_m(e)` kernels by reflexivity, and combines it with the duration-censored stopping certificate when a realized pathwise window is needed. Remaining gap: supply/prove the homogeneous count law, fixed kernels, and stopping-certificate fields for the concrete process/endpoints. |
| Theorem 1 finite-product likelihood | `theorem1_likelihood_product_decomposition_from_primitive_source_model_of_exists_pos_exposure`, `theorem1_source_data_product_decomposition_from_primitive_source_model_of_exists_pos_exposure`, `theorem1_exists_finite_poisson_count_family_for_primitive_source_model_total_count_event_of_exists_pos_exposure`, plus lower-level condition-source/density variants | conditional | Products of finite observed-window cases construct independent finite Poisson count-family witnesses and collapse to one total-count Poisson PMF with a rate-independent residual. The primitive-wrapper product route removes separate rate-independence premises for Condition 1/2. The unchecked part is the compact process/stopping/kernel certificate bundle, not the finite likelihood algebra. |
| Eq. (33)/(34) preprocessing stopping windows | `equation33_nyc_preprocessing_stopping_observation_window`, `equation33_nyc_preprocessing_stopping_observation_window_of_deterministic_endpoints`, `equation33_nyc_preprocessing_stopping_observation_window_of_first_count_arrival`, `equation33_nyc_preprocessing_stopping_observation_window_of_local_count_process_stopping_endpoints`, `equation33_nyc_preprocessing_observation_window_of_local_count_process_at_sample`, `equation33_nyc_zero_report_factorization_from_local_count_process_at_sample`, `equation33_nyc_one_report_factorization_from_local_count_process_at_sample`, `equation33_nyc_multi_report_factorization_from_local_count_process_at_sample`, `equation33_nyc_preprocessing_stopping_observation_window_of_local_count_process`, `equation34_chicago_preprocessing_stopping_observation_window`, `equation34_chicago_preprocessing_stopping_observation_window_of_deterministic_endpoints`, `equation34_chicago_preprocessing_stopping_observation_window_of_first_count_arrival`, `equation34_chicago_preprocessing_stopping_observation_window_of_local_count_process_stopping_endpoints`, `equation34_chicago_preprocessing_observation_window_of_local_count_process_at_sample`, `equation34_chicago_zero_report_factorization_from_local_count_process_at_sample`, `equation34_chicago_one_report_factorization_from_local_count_process_at_sample`, `equation34_chicago_multi_report_factorization_from_local_count_process_at_sample`, `equation34_chicago_preprocessing_stopping_observation_window_of_local_count_process` | formalized | None. Lean proves the min-censored 100-day preprocessing rules define `StoppingObservationWindow`s with nonnegative exposure under generic endpoint stopping premises, fixed endpoint specializations, reusable first-count-arrival certificates, stochastic local-count-process endpoint premises, and deterministic endpoint local-count-process specializations. It also proves the pathwise deterministic `ObservationWindow` projection used by the finite likelihood layer and zero/one/multi-report source-data factorization over the certified pathwise exposure. |
| Appendix Theorem 2 condition-function and jump-time cases | `theorem2_zero_report_condition_functions_factorization`, `theorem2_one_report_condition_functions_factorization`, `theorem2_one_report_jump_time_factorization`, `theorem2_multi_report_condition_functions_factorization`, `theorem2_multi_report_jump_times_factorization`, `theorem2_one_report_proper_window_factorization_row`, `theorem2_multi_report_proper_window_factorization_row`, `theorem2_zero_report_stopping_window_at_sample_factorization_row`, `theorem2_one_report_stopping_window_at_sample_factorization_row`, `theorem2_multi_report_stopping_window_at_sample_factorization_row` | formalized | None. Encodes the paper's `g(s)`, `h_m(e)`, survival-integral bookkeeping, zero-report observation windows, observed jump-time exposure identities, ordered-window derivation of nonzero exposure plus nonnegative gaps/tails before converting to source data, and zero/one/multi source-data factorization over deterministic windows realized by stopping observation windows. |
| Appendix Theorem 2 zero-report case, Eq. (20) | `theorem2_zero_report_source_case` | formalized | None. Source-shaped `g(s) h_m(e) exp(-lambda(e-s))` case algebra. |
| Appendix Theorem 2 one-report case, Eq. (26) | `theorem2_one_report_source_case` | formalized | None. Source-shaped `lambda exp(-lambda(e-s))` case algebra; residual absorbs `1/(e-s)`. |
| Appendix Theorem 2 multi-report case, Eq. (32) | `theorem2_multi_report_source_case` | formalized | None. Source-shaped `lambda^M exp(-lambda(e-s))` case algebra with corrected residual for `M > 1`. |
| Appendix Theorem 2 interarrival collection, Eq. (24)/(30) to Eq. (25)/(31) | `theorem2_interarrival_kernel_collection`, `theorem2_one_report_kernel_collection`, `theorem2_multi_report_kernel_collection` | formalized | None. Reusable interarrival-density product and terminal no-arrival tail collect to the source `lambda^M exp(-lambda exposure)` shape. |
| Appendix Theorem 2 process-kernel factorization, Eq. (18)/(23)/(29) to Eq. (20)/(26)/(32) | `theorem2_zero_report_process_kernel_source_case`, `theorem2_one_report_process_kernel_source_case`, `theorem2_multi_report_process_kernel_source_case` | formalized | None. Starts from the explicit no-arrival/interarrival source kernels and derives the Poisson PMF residual factorization. |
| Appendix Theorem 2 case algebra | `theorem2_corrected_case_factorization` | formalized | None. Uses the corrected residual factor `M! / exposure^M`. The printed `M > 1` residual in Appendix B.2 appears to have the reciprocal factor. |
| Eq. (3), MLE score equation | `equation3_mle_score_equation` | formalized | None. Proves the displayed ratio solves the Poisson score equation under nonzero total count/exposure. |
| Eq. (3), global MLE log-likelihood optimality | `equation3_mle_global_logLikelihood_max` | formalized | None. Proves the displayed ratio globally maximizes the rate-dependent Poisson log-likelihood kernel over positive rates when total count and exposure are positive. |
| Eq. (3), finite-product likelihood kernel | `equation3_product_likelihood_raw_shape` | formalized | None. Product of incident Poisson factors equals a rate-independent residual times `rate^(sum counts) * exp(-rate * sum exposure)`. |
| Eq. (3), total-count PMF likelihood kernel | `equation3_product_likelihood_total_pmf` | formalized | None. Product of incident Poisson factors equals a rate-independent residual times one Poisson PMF at total exposure and total count. |
| Eq. (5), Poisson regression log-link | `equation5_poisson_regression_rate_formula` | formalized | None. Exact log-link formula; the implementation also proves positivity of the exponential rate. |
| Eq. (6), Poisson regression incident likelihood | `equation6_poisson_regression_likelihood_formula` | formalized | None. Direct specialization of the source PMF. |
| Eq. (7), zero-inflated likelihood | `equation7_zero_inflated_likelihood_zero`, `equation7_zero_inflated_likelihood_positive_count`, `equation7_zero_inflated_regression_likelihood_zero`, `equation7_zero_inflated_regression_likelihood_positive_count`, `equation7_zero_inflated_likelihood_nonnegative` | formalized | None. Generic and regression-rate-substituted mixture cases. Nonnegativity assumes `0 <= gamma <= 1` and nonnegative Poisson mean. |

## Main Remaining Work

1. Prove or supply the compact process/stopping/kernel certificate bundle
   behind Appendix Lemma 2 and Theorem 2: a
   `HomogeneousPoissonCountingProcessByLaw`, fixed paper `g`/`h_m` kernels,
   and `DurationCensoredFirstCountObservationCertificate` fields for the
   concrete endpoints. The min-censoring closure for Eq. (33)/(34) endpoint
   rules is now checked, including deterministic endpoint, first-count-arrival,
   and local count-process certificate variants. Shrinking this boundary
   further would require deeper reusable continuous-time process and natural
   filtration library work.
2. Strengthen Lemma 1 further only if needed by deriving the IID
   unit-interval observed-count and one-period-mean premises from a Poisson
   thinning/steady-state model; the current LLN route, finite-duration
   mixture algebra, finite-duration thinning count law, and
   non-identifiability algebra are Lean-checked.
3. Run the over-30-row statement/assumption/provenance audits before making any
   completion claim.

## Artifacts

- Implementation theorem file: `papers/LBG24SpatialUnderreporting/MainTheorems.lean`
- Human-facing theorem file: `papers/LBG24SpatialUnderreporting/PaperInterface.lean`
- Assumption/proof-boundary file: `papers/LBG24SpatialUnderreporting/Assumptions.lean`
- Outside-Lean proof plan: `papers/LBG24SpatialUnderreporting/FORMALIZATION_PLAN.md`
- Machine-readable status: `papers/LBG24SpatialUnderreporting/status.json`
- Dependency DAG: `papers/LBG24SpatialUnderreporting/DependencyDAG.tex`
- Final validation report: `papers/LBG24SpatialUnderreporting/FINAL_VALIDATION_REPORT.md`
- Recursive source-record audit: `papers/LBG24SpatialUnderreporting/source_record_audit.json`

## Validation To Run Later

```bash
lake build LBG24SpatialUnderreporting
python3 scripts/review_dashboard.py --paper LBG24SpatialUnderreporting --precheck
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper LBG24SpatialUnderreporting --out papers/LBG24SpatialUnderreporting/source_record_audit.json
python3 scripts/audit_repository.py --paper LBG24SpatialUnderreporting --paper-closeout --include-active --info-limit 0
python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0
```
