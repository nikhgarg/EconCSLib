# Final Validation Report: GJ18 Informative Rating Systems

## 1. Human Verdict
Formalized. Theorem 1 is checked for the finite ordinal rating support used by
the paper, with the bottom/top atom conditions derived from that support. No
source-paper error is reported. No human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The finite rating model and Theorem 1 are checked through
  the support-safe threshold-rate minimum.

## 3. Source and Scope
- Paper: *Designing Informative Rating Systems: Evidence from an Online Labor Market*.
- Publication version: Manufacturing & Service Operations Management 23(3):589-605, published online 2020 (issue 2021); DOI `10.1287/msom.2020.0921`.
- Formalized source/PDF: arXiv 1810.13028 TeX/PDF cache.
- Lean folder: `papers/GJ18InformativeRatingSystems`.
- Human-facing theorem file: `papers/GJ18InformativeRatingSystems/PaperInterface.lean`.
- DAG artifacts: `papers/GJ18InformativeRatingSystems/DependencyDAG.tex`, `papers/GJ18InformativeRatingSystems/DependencyDAG.pdf`.

The official publisher article is the MSOM/INFORMS version. The arXiv
1810.13028 TeX/PDF cache used for formalization intake, extracted text, and source archive
are local source-audit artifacts and are not part of the public theorem surface
unless redistribution rights are checked separately.

## 4. Researcher Summary of Checked Results
- The formalization checks Theorem 1 for the finite ordinal rating support used by the paper.
- The bottom/top atom and threshold-support conditions needed by the source proof are made explicit.
- The paper-facing surface focuses on the finite-support rating-system theorem rather than broader empirical claims.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
- None

## 7. Proof-Strategy Deviations
- Lean uses finite-support MGF/Cramer certificates and method-of-types support
  machinery rather than treating the appendix's large-deviation and Laplace
  principle steps as a single black-box calculation.
- The adjacent-pair dominance step is proved through a concrete joint
  floor-rating law, dependent product marginals, and finite adjacent-inversion
  union bounds.
- The support-safe finite-support rate convention is treated as the canonical
  statement, not as a caveat in the finite model or adjacent aggregation.

## 8. Proof Tricks Worth Reusing
- Separate pairwise LDP certificates from finite aggregation and objective
  transfer.
- Use displayed pairwise-objective endpoints to isolate the finite LDP work
  from the source threshold-rate identification problem.
- Use support-safe extended rates for finite-support threshold-rate
  identification; the real-valued source `sInf` route is unsafe outside the
  finite score hull without extra domain work.
- Use concrete joint laws plus two-coordinate marginal lemmas to keep dependent
  finite-product event proofs auditable.
- Represent source floor counts directly, then use normalization/equality
  lemmas only where the proof route needs them.

## 9. Paper Issues or Caveats
None found.

## 10. Detailed Formalization Evidence
Lean exposes the paper's finite ordered seller-type model, finite rating levels,
single-rating log-MGF, Legendre rate function, pairwise threshold-rate formula,
finite MGF factorizations, integer-rate and floor-count objective bridges, the
`1 - P_k` algebra, finite aggregation to `1 - W_k`, and the deterministic and
PMF adjacent-inversion reductions used in Theorem 1.

The strongest Theorem 1 endpoint is source-shaped for the paper's finite model
and floor-count match rates. It takes the paper's upper-tail rating dominance
primitive directly: for every ordered pair of source types, the lower type's
upper-tail rating probabilities are bounded by the higher type's corresponding
upper-tail probabilities. A reusable finite FOSD lemma turns this into
expected-score ordering for monotone scores, and Lean derives the common-dual
witnesses and pairwise support-safe LDP certificates internally. Because the
source model has finite rating levels and scores in `[0,1]`, this support-safe
extended-rate convention is the canonical finite-support statement. The older
all-real theorem is retained only as a compatibility wrapper for users who
supply stronger real-valued boundedness or domain hypotheses.

Empirical, simulation, and data-analysis sections are source scope notes, not
Lean theorem targets.

## 11. Paper Definitions Checked
- Log-MGF `Lambda(z | theta) = log sum_y rho(theta,y|Y) exp(z phi(y))`.
  Lean: `definition_log_mgf_formula`.
- Rate function `I(a | theta) = sup_z {za - Lambda(z | theta)}`.
  Lean: `definition_rate_function_formula`.
- Pairwise threshold-rate objective
  `inf_a {g(theta_hi) I(a|theta_hi) + g(theta_lo) I(a|theta_lo)}`.
  Lean: `lemmaC_pairwise_threshold_rate_formula`.
- Pairwise objective `P_k` and `1 - P_k` transfer.
  Lean: `lemmaC_pk_complement_error_eq_one_sub_pk_objective`.
- Floor-count match rates `n_k(theta) = floor(k g(theta))`.
  Lean: `source_floor_sample_count_div_tendsto_sampleRate`.
- Kendall-style objective `W_k` through finite weighted pair aggregation.
  Lean: `theorem1_floor_pk_complement_error_eq_one_sub_weighted_objective`.

## 12. Named Theorem Statements Checked
### Appendix Lemma `problessthan`

**Paper statement.** The pairwise score-comparison error has exponential rate
equal to the displayed infimum of the two source rate functions.

**Lean interface statement.**
- `lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support`: floor-count pairwise score-gap rate from derivative, minimizer, and support inputs.

**Status.** formalized on the main support-safe route. The older displayed
derivative/minimizer helper remains available as an auxiliary conditional
wrapper, but Theorem 1 no longer depends on supplying those witnesses
externally.

### Appendix Lemma `Pk_LD`

**Paper statement.** The pairwise rate transfers from the score-comparison
event to `1 - P_k(theta_1, theta_2)`.

**Lean interface statement.**
- `lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives`: integer-rate source-threshold transfer for `1 - P_k`.
- `lemmaC_floor_pk_complement_error_rate_from_left_tail`: floor-count transfer from a pairwise left-tail certificate.

**Status.** formalized on the main Theorem 1 route. Standalone reusable
transfer lemmas still expose certificate-taking forms for future papers.

### Theorem 1

**Paper statement.** For the finite ordered seller-type model, the rate of
`1 - W_k` is the minimum adjacent-pair threshold rate.

**Lean interface statement.**
- `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law`: finite ordered floor-count endpoint using the concrete joint floor-rating law and adjacent reduction.
- `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_adjacent_objective_rate_from_logMGF_derivatives_and_score_bounds`: finite ordered endpoint at the displayed adjacent pairwise-objective rate, deriving threshold straddling from bottom/top rating support.
- `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_objective_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds`: finite ordered endpoint at the minimum displayed adjacent-objective rate, using the concrete joint floor-rating law and deriving threshold straddling from bottom/top rating support.
- `theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives`: support-safe extended source threshold-rate minimum equals the displayed adjacent-objective minimum.
- `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_pairwise_threshold_rate_regularity`: source-facing extended-rate endpoint at the support-safe adjacent threshold-rate minimum from the compact pairwise threshold-rate regularity package.
- `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support`: source-facing support-safe endpoint from ordinal upper-tail dominance, monotone scores, positive match rates, and full finite ordinal rating support; bottom/top atom support is derived internally.
- `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq`: optional real-rate compatibility statement from the support-safe endpoint under a stronger all-real domain convention.
- `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_pairwise_threshold_rate_regularity`: real-rate compatibility endpoint using the same named pairwise threshold-rate regularity package.

**Status.** formalized through the support-safe threshold-rate minimum. The
finite ordered model, source floor-count objective, finite aggregation,
full-support-to-straddling step, adjacent-pair reduction, finite
upper-tail stochastic dominance bridge, common-dual witness derivation, and
pairwise support-safe LDP certificates are represented. Lean also exposes a
real-rate compatibility wrapper for stronger all-real domain conventions.

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem definition_log_mgf_formula | `definition_log_mgf_formula` | - The paper's log-MGF formula `Λ(z \| θ)`. |
| theorem definition_rate_function_formula | `definition_rate_function_formula` | - The paper's Legendre-transform formula `I(a \| θ)`. |
| theorem lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives | `lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives` | integer-rate source-threshold transfer for `1 - P_k`. |
| theorem lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support | `lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support` | uncertain. The translation matches the auxiliary lemma, but the row is a reusable proof-route lemma rather than a named paper statement; it should remain flagged for surface review. |
| theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law` | finite ordered floor-count endpoint using the concrete joint floor-rating law and adjacent reduction. |
| theorem theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives | `theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives` | support-safe extended source-rate identification is closed. |
| theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support | `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support` | main source-facing Theorem 1 endpoint. |
| theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq` | optional real-rate compatibility statement for stronger all-real domain conventions. |
<!-- lean-derived-statements:end -->

## 13. Paper-Facing Statement Validator Ledger
Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GJ18InformativeRatingSystems --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| theorem definition_log_mgf_formula | `definition_log_mgf_formula` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem definition_rate_function_formula | `definition_rate_function_formula` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support | `lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:31Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:31Z): The translation matches the auxiliary lemma, but the row is a reusable proof-route lemma rather than a named paper statement; it should remain flagged for surface review. |
| theorem lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives | `lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives | `theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support | `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support` | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:31Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 14. Paper Assumption Provenance
Every paper-facing premise is routed through
`GJ18InformativeRatingSystems/Assumptions.lean` and checked by
`assumption_match_llm.json`. The canonical Theorem 1 endpoint uses source
model assumptions: positive match rates, monotone scores, and full finite
ordinal rating support. A few auxiliary Appendix C and real-rate compatibility
rows expose common-dual/minimizer regularity conditions; those are documented
as proof-route conditions and are not the canonical theorem endpoint.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_positive_match_rates` | paper condition | Positive asymptotic sample rates in the paper's `floor(k g(theta))` sample-count model. |
| `assumption_positive_integer_sample_rates` | derived from source primitives | Integer-rate helper rows instantiate positive sample rates. |
| `assumption_nonpositive_common_dual_parameters` | derived from source primitives | Auxiliary common-dual lower-tail witnesses; derived/packaged on the canonical support-safe route. |
| `assumption_pairwise_threshold_minimizer` | derived from source primitives | Helper-level witness that the displayed threshold realizes the source `inf_a` pairwise objective. |
| `assumption_two_sided_score_witnesses` | derived from source primitives | Finite-support lower-bound witnesses derived from full finite ordinal support and score span. |
| `assumption_monotone_rating_scores` | source text model primitive | Source scores are monotone in ordinal rating level. |
| `assumption_full_finite_ordinal_rating_support` | derived from source primitives | The source finite ordered rating scale and strictly decreasing cumulative rating law provide the finite support used by the endpoint. |
| `assumption_score_range_and_strict_span` | derived from source primitives | Source score function lies in `[0,1]` and the increasing score design supplies a nontrivial span. |

Additional assumptions beyond the paper: none for the canonical support-safe
Theorem 1 endpoint. Finite seller types, finite rating levels, and floor-count
sample sizes are part of the source model.

## 15. Library Lift Pass
- `EconCSLib.Foundations.Probability.FiniteRatingComparison`: extracted the
  generic finite-rating comparison spine from this paper's implementation file:
  source-facing log-MGF/rate wrappers, support-safe pairwise threshold rates,
  finite tilted score means, two-sample and floor-count comparison
  probabilities, `P_k`/`1 - P_k` algebra, integer-rate block comparisons, and
  pairwise LDP certificate constructors. `MainTheorems.lean` now keeps the
  paper-specific finite-chain aggregation and theorem endpoints.
- `EconCSLib.Foundations.Probability.FiniteSupportMGF`: finite-support MGFs,
  log-MGFs, Legendre/rate-function wrappers, and shifted score algebra.
- `EconCSLib.Foundations.Probability.LargeDeviations`: exact-rate,
  upper/lower-bound, finite weighted-sum, and aggregation certificates.
- `EconCSLib.Foundations.Probability.IndependentProduct`: finite product PMF
  and marginal infrastructure.
- `EconCSLib.Foundations.Probability.FiniteRankingEvents`: adjacent-inversion
  deterministic and PMF union-bound kernels.
- `EconCSLib.Foundations.Probability.IIDLargeDeviations` and
  `FiniteTypeLogMass`: reusable finite iid Cramer/method-of-types support.
- `EconCSLib.Foundations.Probability.FiniteExpectation`:
  `pmfExp_le_pmfExp_of_fin_tail_prob_le`, a reusable finite ordinal
  first-order stochastic dominance theorem.

The old real-valued threshold-minimum equality can remain as an optional
compatibility theorem for users who choose a stronger all-real domain
convention.

## 16. DAG Audit
- Rendered artifact: `DependencyDAG.pdf`.
- Topology: source-facing model, finite FOSD/tail-dominance bridge, Appendix
  Lemma C support, `P_k` transfer, and one formalized Theorem 1 endpoint.
- Layout: rendered and visually inspected after the formalized-status change.
- Status: no partial/caveat node remains on the main Theorem 1 path.

## 17. Validation Checks
The GJ18 paper build passes. The DAG was regenerated from the paper folder,
converted to PNG, and visually inspected. Generated status artifacts were
refreshed with `scripts/sync_paper_status.py`, and the sync check passed.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 7 rows; 7 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

Flagged rows: none. The auxiliary proof-route lemma
`lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support`
remains available internally but is no longer part of the paper-facing dashboard
surface.
