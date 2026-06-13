# Final Validation Report: LMMS04 Fair Division

## 1. Human Verdict

- Lean formalization status: partially formalized.
- Human dashboard review status: 0/31 rows reviewed; 0 stale; 0 mismatches.
- LLM statement-translation audit: 42/42 row-local LLM-as-judge statement rows match, including 11 explicit assumption/dependency rows; 0 stale, missing, uncertain, or mismatch rows.
- Paper correctness verdict: no fatal error found. Formalization exposed several implicit modeling choices and one source-prose typo in the Lemma 2.4 partition argument.
- Qualitative proof verdict: Sections 2 and 4 follow the paper-level proof structure. Section 3 is intentionally stopped at a reusable complexity boundary.
- Lean footprint: 80,424 paper-local Lean lines across 24 files; `PaperInterface.lean` has 249 lines and 31 review rows.
- Human summary: Sections 2 and 4 are closed; Section 3 has query/descent/rounded-search support. The PTAS/FPTAS runtime layer needs reusable fixed-dimension IP complexity infrastructure.

<!-- transitive-source-premise-audit:start -->
### Axiom, Premise, And Source-Hygiene Audit

The current axiom/premise/source-hygiene audit does not yet pass for full-status provenance. It uses Lean-native #print axioms for transitive proof debt, expanded paper-facing signatures for visible premises, and source-assumption ledgers for any non-derived assumptions.

Current result: the Section 3 runtime/search layer and some rounded-IP/counterexample endpoints remain certificate boundaries; Sections 2 and 4 stay formalized at their existing boundary.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

- Paper: *On Approximately Fair Allocations of Indivisible Goods*
- Authors: Richard J. Lipton, Evangelos Markakis, Elchanan Mossel, and Amin Saberi
- Source version: EC 2004 paper, ACM DOI 10.1145/988772.988792
- Lean folder: `LMMS04FairDivision/`
- Human-facing theorem file: `LMMS04FairDivision/PaperInterface.lean`
- DAG artifacts: `LMMS04FairDivision/DependencyDAG.tex`, `LMMS04FairDivision/DependencyDAG.pdf`
- Supporting audit ledger: `LMMS04FairDivision/POST_FORMALIZATION_AUDIT.md`

## 3. What Has Been Proven

The formalization closes the Section 2 finite-allocation envy interface, the envy-cycle reduction, the bounded-envy allocation theorem, and the real-interval/atom-bound route used for the measure-valued allocation theorem. It also closes the Section 4 finite truthfulness results: the no-truthful-envy-free/minimum-envy counterexample route and the uniform randomized mechanism with its explicit probability bound.

Section 3 has substantial formal content but remains partial at the runtime boundary. The Lean development includes adaptive-query lower-bound wrappers, the Graham-scheduling consequence used by the paper, rounded type/value-pair search infrastructure, bounded-optimal allocation certificates, and ratio-transfer lemmas. The final PTAS/FPTAS theorem is not closed because the reusable fixed-dimension integer-program runtime theorem is not yet in the library.

## 4. Paper Assumption Provenance

> Axiom/premise/source-hygiene audit update (2026-06-12): `assumption_match_llm.json` now records per-premise judgments for this paper's `Assumptions.lean` ledger. Current result: 28/28 explicit proof premises in the compact paper-facing surface are matched to, or derived from, source-model conditions. The selected min/max rounded-type identification helper is no longer exposed as a paper-facing row; it remains available in `ProofInterface.lean` for proof engineering.

Every non-derived paper-facing premise is routed through
`LMMS04FairDivision/Assumptions.lean` and checked by
`assumption_match_llm.json`. Most rows are theorem-domain conditions already
present in the source structure: positive error parameters, positive rounding
and load scales, finite duplicate-free goods enumerations, positive small-good
values, normalized random-allocation item weights, and atom-bound/real-support
conditions for the measure-valued theorem.

No compact paper-facing premise is currently accepted as an extra proof-route
assumption. The older generic Claim 3.4 helper that assumed a
ratio-nonincreasing reallocation, and the selected min/max rounded-type helper,
are not part of the human-facing review surface. The active Claim 3.4
paper-facing rows use the exact-allocation and finite identical-utilities
endpoints, where the ratio-nonincreasing descent is derived from concrete
min/max source moves.

Two additional dependencies are external theorem/library boundaries rather
than paper assumptions:

- Theorem 3.2 cites Graham's scheduling theorem. Lean proves the fair-division
  consequence from that scheduling theorem.
- Theorem 3.3's final PTAS/FPTAS runtime conclusion needs reusable
  fixed-dimension integer-program runtime infrastructure. In Lean this is
  currently represented by `EconCSLib.Complexity.ExternalSolverConsequence`.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_nonnegative_alpha_bound` | paper condition | Nonnegative alpha for bounded-envy finite allocations. |
| `assumption_duplicate_free_goods_enumeration` | paper condition | Constructive algorithm list enumerates the finite good set. |
| `assumption_positive_atom_bound` | paper condition | Positive atom-size bound for Theorem 2.3/Lemma 2.4. |
| `assumption_ptas_error_parameter_range` | paper condition | Positive PTAS/FPTAS error parameter, with finite wrapper range. |
| `assumption_external_graham_scheduling_boundary` | external theorem dependency | Graham scheduling theorem is cited externally by the source paper; Lean proves the fair-division consequence from it. |
| `assumption_fixed_dimension_ip_runtime_boundary` | partial library boundary | Fixed-dimension IP runtime theorem remains reusable library infrastructure work. |
| `assumption_positive_rounding_and_load_parameters` | paper condition | Positive load and rounding parameters in Section 3. |
| `assumption_base_load_at_most_rounded_average` | paper condition | Capped rounded-supply helper domain. |
| `assumption_claim34_positive_small_goods_domain` | paper condition | Claim 3.4 small-good model domain. |
| `assumption_additive_transfer_load_window_conditions` | paper condition | Lemma 3.5 load-window transfer conditions. |
| `assumption_uniform_random_weight_normalization` | paper condition | Theorem 4.2 normalized nonnegative additive utilities. |

## 5. Proof-Strategy Deviations

- Theorem 4.1 is proved with a smaller finite counterexample than the source
  exposition. This is sufficient for the impossibility theorem.
- Claim 3.4 required a more explicit finite-descent proof than the prose
  presentation. The formal proof separates high-source moves from low-only
  tie-breaking moves.
- Theorem 4.2 is recorded as the finite inequality used by the proof rather
  than a separate asymptotic Big-O wrapper.

## 6. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 7. Library Lift Pass

None separately recorded in the existing report.

## 8. DAG Audit

No separate DAG audit note is recorded in the existing report.

## 9. Conditional Results and Remaining Gaps

The remaining mathematical gap is not another fair-division lemma. It is the
general computational-complexity theorem saying that the fixed-dimension IP
instances generated by the formalized rounded search can be solved within the
runtime needed for the paper's PTAS/FPTAS conclusion. The preferred next step
is to discharge `ExternalSolverConsequence` through reusable complexity and
optimization infrastructure, then expose the final Theorem 3.3 runtime theorem.

## 10. Suspected Paper Errors or Inconsistencies

- The Lemma 2.4 partition discussion contains a source-prose typo around the
  "minimum possible value" wording. The Lean proof uses the corrected
  first-crossing/maximal-cut route.
- No fatal correctness issue was found.

## 11. Validation Checks

Recent checks built the LMMS paper module, `PaperInterface.lean`, the Section 3
support modules, the relevant fair-division/probability support, the dependency
DAG, and the review dashboard. The dashboard reads 32 source-facing paper rows
from `status.json` plus 12 explicit assumption/dependency rows from
`Assumptions.lean`; it currently reports no mismatched or stale rows, but no
human review entries have been saved.

### Statement Translation Audit

Audit date: 2026-06-12.
Scope: current dashboard rows from `PaperInterface.lean` and `Assumptions.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment. Premise-level source provenance for assumption rows is recorded separately in `assumption_match_llm.json`.

Summary: 44 rows; 44 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none.

Flagged rows: none.

## 12. Final Verdict

LMMS04 is suitable as a public partial formalization. Sections 2 and 4 are
closed in the current paper-facing model, and Section 3 exposes substantial
verified fair-division and rounded-search infrastructure. The status remains
partial because the final PTAS/FPTAS runtime claim depends on a reusable
fixed-dimension IP complexity theorem that is not yet present in the library.

- Completion status: partially formalized.
- Summary: Sections 2 and 4 are closed; Section 3 has query/descent/rounded-search support. The PTAS/FPTAS runtime layer needs reusable fixed-dimension IP complexity infrastructure.

## 13. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def envy | `envy` | - Envy of agent `i` toward agent `j`: positive part of the value difference. |
| def envyFree | `envyFree` | - Envy-free allocations have no positive envy between any ordered pair. |
| def envyBoundedBy | `envyBoundedBy` | - Bounded-envy predicate used in Theorem 2.1. |
| def maxMarginal | `maxMarginal` | - Maximum marginal item value. |
| def isAllocationOf | `isAllocationOf` | - Allocation of exactly the specified finite set of goods. |
| abbrev lemma2_2_acyclic_reduction | `lemma2_2_acyclic_reduction` | - Lemma 2.2: envy-cycle elimination produces an acyclic envy graph. |
| abbrev theorem2_1_bounded_envy_allocation_exists | `theorem2_1_bounded_envy_allocation_exists` | - Theorem 2.1: bounded-envy allocation existence. |
| abbrev theorem2_1_alpha_bounded_allocation_exists | `theorem2_1_alpha_bounded_allocation_exists` | - Theorem 2.1 alpha-bounded form. |
| abbrev theorem2_1_algorithm_correct_list_toFinset | `theorem2_1_algorithm_correct_list_toFinset` | - Theorem 2.1 constructive list algorithm form. |
| abbrev theorem2_3_real_interval_supported_atom_bound | `theorem2_3_real_interval_supported_atom_bound` | - Theorem 2.3 real-interval supported atom-bound endpoint. |
| abbrev theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries | `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries` | - Theorem 3.1 adaptive-query lower bound. |
| abbrev theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries | `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries` | - Theorem 3.1 adaptive-query ratio lower bound. |
| abbrev theorem3_2_graham_certificate_to_envy_ratio_bound | `theorem3_2_graham_certificate_to_envy_ratio_bound` | - Theorem 3.2 Graham-certificate fair-division consequence. |
| abbrev theorem3_2_graham_factor_eq_seven_fifths | `theorem3_2_graham_factor_eq_seven_fifths` | - Theorem 3.2 evaluates the Graham factor as seven fifths. |
| abbrev theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | - Theorem 3.3 conditional fixed-dimension IP summary. |
| abbrev theorem3_3_claim34_fixed_rounding_ratio_endpoint | `theorem3_3_claim34_fixed_rounding_ratio_endpoint` | - Claim 3.4 fixed-rounding ratio endpoint. |
| abbrev theorem3_3_claim34_capped_weighted_supply_ratio_endpoint | `theorem3_3_claim34_capped_weighted_supply_ratio_endpoint` | - Claim 3.4 capped weighted-supply endpoint. |
| abbrev claim3_4_bounded_optimal_certificate | `claim3_4_bounded_optimal_certificate` | - Claim 3.4 bounded-optimal certificate. |
| abbrev claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods | `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods` | - Claim 3.4 exact-allocation bounded optimum endpoint. |
| abbrev claim3_4_bounded_optimal_of_identical_utilities_model | `claim3_4_bounded_optimal_of_identical_utilities_model` | - Claim 3.4 identical-utilities bounded optimum endpoint. |
| abbrev theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads | `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads` | - Theorem 3.3 additive-load ratio transfer. |
| abbrev lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads | `lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads` | - Lemma 3.5 additive transfer endpoint. |
| theorem directMechanism_fields | `directMechanism_fields` | - Direct mechanisms are no-transfer allocation rules on reported additive valuations. |
| theorem randomizedDirectMechanism_fields | `randomizedDirectMechanism_fields` | - Randomized direct mechanisms are lotteries over allocations on reported additive valuations. |
| def truthful | `truthful` | - Dominant-strategy truthfulness for direct fair-division mechanisms. |
| def randomizedTruthful | `randomizedTruthful` | - Expected-utility truthfulness for randomized direct mechanisms. |
| theorem theorem4_1_source_goods_content | `theorem4_1_source_goods_content` | - The Theorem 4.1 source instance has two players and the paper's finite egg/goods configuration. |
| theorem theorem4_1_true_report_formula | `theorem4_1_true_report_formula` | - The Theorem 4.1 truthful report has the concrete additive utilities used in the source counterexample. |
| abbrev theorem4_1_source_not_truthful_envy_free_whenever_exists | `theorem4_1_source_not_truthful_envy_free_whenever_exists` | - Theorem 4.1 envy-free mechanism impossibility. |
| abbrev theorem4_1_source_minimum_envy_not_truthful | `theorem4_1_source_minimum_envy_not_truthful` | - Theorem 4.1 minimum-envy mechanism impossibility. |
| abbrev theorem4_2_uniform_random_mechanism_truthful | `theorem4_2_uniform_random_mechanism_truthful` | - Theorem 4.2 uniform-random mechanism truthfulness. |
| abbrev theorem4_2_uniform_random_max_envy_probability_bound | `theorem4_2_uniform_random_max_envy_probability_bound` | - Theorem 4.2 uniform-random maximum-envy probability bound. |
<!-- lean-derived-definitions:end -->

## 14. Named Theorem Statements Checked

### Theorem-by-Theorem Validation

| Paper item | Status | Statement match | Notes |
|---|---|---|---|
| Section 2 definitions: allocations, envy, envy-free, bounded envy, maximum marginal value | formalized | exact | Finite-agent/finite-good paper interface. |
| Lemma 2.2, envy-cycle elimination | formalized | exact | Gives an acyclic envy graph while preserving allocation and envy bound. |
| Theorem 2.1, bounded-envy allocation existence | formalized | exact for finite goods | Includes constructive algorithm correctness for the finite allocation model. |
| Lemma 2.4 and Theorem 2.3, measure-valued utilities | formalized | model-explicit | Lean states the real-supported interval/atom-bound hypotheses explicitly and proves the finite partition route used by the paper. |
| Theorem 3.1, query lower bound | formalized | source-shaped | Lean proves the hard-family/counting/transcript lower-bound wrapper under the source asymptotic condition; the standalone binomial-to-exponential estimate is not separately formalized. |
| Theorem 3.2, Graham 1.4 approximation | partial external dependency | citation wrapper | Lean proves the fair-division consequence from a Graham scheduling certificate, not Graham's external scheduling theorem itself. |
| Theorem 3.3, PTAS/FPTAS for identical utilities | partially formalized | conditional | Finite rounded-type, value-pair search, IP-certificate, source-output, and ratio-transfer layers are formalized; the final fixed-dimension IP runtime theorem remains external. |
| Claim 3.4, bounded optimal allocation under small goods | formalized | finite exact-allocation and identical-utilities versions | Lean proves the finite descent and exact-allocation/model wrappers; the old generic nonincreasing-reallocation helper is no longer part of the paper-facing surface. |
| Lemma 3.5, rounded-allocation transfer | partially formalized | algebraic transfer closed | The arithmetic ratio-transfer lemmas are formalized; the full algorithmic/runtime packaging remains tied to Theorem 3.3's external solver boundary. |
| Theorem 4.1, no truthful minimum-envy mechanism | formalized | proof-strengthening | Lean uses a two-player/eight-egg finite counterexample with the same manipulation structure as the paper's larger example. |
| Theorem 4.2, randomized truthful allocation bound | formalized | finite explicit bound | Lean proves the independent uniform assignment truthfulness and the explicit Chebyshev/union-bound probability inequality. |

## 15. Paper-Facing Statement Validator Ledger

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| abbrev claim3_4_bounded_optimal_certificate | `claim3_4_bounded_optimal_certificate` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods | `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev claim3_4_bounded_optimal_of_identical_utilities_model | `claim3_4_bounded_optimal_of_identical_utilities_model` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem directMechanism_fields | `directMechanism_fields` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z): The revised Lean review row spells out the source equation or condition directly, rather than exposing only a function signature or opaque constructor. |
| def envy | `envy` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def envyBoundedBy | `envyBoundedBy` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def envyFree | `envyFree` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def isAllocationOf | `isAllocationOf` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma2_2_acyclic_reduction | `lemma2_2_acyclic_reduction` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads | `lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def maxMarginal | `maxMarginal` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem randomizedDirectMechanism_fields | `randomizedDirectMechanism_fields` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z): The revised Lean review row spells out the source equation or condition directly, rather than exposing only a function signature or opaque constructor. |
| def randomizedTruthful | `randomizedTruthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_1_algorithm_correct_list_toFinset | `theorem2_1_algorithm_correct_list_toFinset` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_1_alpha_bounded_allocation_exists | `theorem2_1_alpha_bounded_allocation_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_1_bounded_envy_allocation_exists | `theorem2_1_bounded_envy_allocation_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem2_3_real_interval_supported_atom_bound | `theorem2_3_real_interval_supported_atom_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries | `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries | `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_2_graham_certificate_to_envy_ratio_bound | `theorem3_2_graham_certificate_to_envy_ratio_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_2_graham_factor_eq_seven_fifths | `theorem3_2_graham_factor_eq_seven_fifths` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_3_claim34_capped_weighted_supply_ratio_endpoint | `theorem3_3_claim34_capped_weighted_supply_ratio_endpoint` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_3_claim34_fixed_rounding_ratio_endpoint | `theorem3_3_claim34_fixed_rounding_ratio_endpoint` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads | `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem4_1_source_goods_content | `theorem4_1_source_goods_content` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z): The revised Lean review row spells out the source equation or condition directly, rather than exposing only a function signature or opaque constructor. |
| abbrev theorem4_1_source_minimum_envy_not_truthful | `theorem4_1_source_minimum_envy_not_truthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem4_1_source_not_truthful_envy_free_whenever_exists | `theorem4_1_source_not_truthful_envy_free_whenever_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem4_1_true_report_formula | `theorem4_1_true_report_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z): The revised Lean review row spells out the source equation or condition directly, rather than exposing only a function signature or opaque constructor. |
| abbrev theorem4_2_uniform_random_max_envy_probability_bound | `theorem4_2_uniform_random_max_envy_probability_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem4_2_uniform_random_mechanism_truthful | `theorem4_2_uniform_random_mechanism_truthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def truthful | `truthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:43Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.
