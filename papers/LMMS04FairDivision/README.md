# On Approximately Fair Allocations of Indivisible Goods

## Public Status

This folder is intentionally public as a partial formalization. The completed
surface covers Sections 2 and 4 and a large part of the Section 3 finite
rounding/search machinery. The remaining paper-facing gap is the final
PTAS/FPTAS runtime conclusion for Theorem 3.3, which is held behind the explicit
`EconCSLib.Complexity.ExternalSolverConsequence` boundary rather than hidden as
an informal assumption. The intended next step is reusable fixed-dimension IP
complexity infrastructure that can also support future EC formalizations.

## Source Version

- Paper: *On Approximately Fair Allocations of Indivisible Goods*
- Authors: Richard J. Lipton, Evangelos Markakis, Elchanan Mossel, and Amin Saberi
- Version formalized: EC 2004 paper, ACM DOI 10.1145/988772.988792
- Official URL: https://dl.acm.org/doi/10.1145/988772.988792
- Official PDF: https://dl.acm.org/doi/pdf/10.1145/988772.988792
- Public course PDF mirror: https://www.cs.cmu.edu/~arielpro/15896s15/docs/paper12a.pdf
- Accessed: 2026-04-23

The PDF is cached locally as `LMMS04FairDivision.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache
`LMMS04FairDivision.txt` is used for named-statement searches; refresh it only
if the source PDF changes. Use the ACM DOI/PDF above as the source version; the
public mirror is listed only for easier access.

## Central Theorem File

- `LMMS04FairDivision/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Detailed envy-graph,
cycle-elimination, potential, and allocation lemmas live in
`IndivisibleGoods.lean`.

## Pickup Path

- Transition plan: `TRANSITION_PLAN_2026-05-26.md`.
- Start next from `START_HERE_NEXT_AGENT.md`.
- Full current handoff: `HANDOFF_2026-05-25.md`.

The active Theorem 3.3 seam is two-scale: the original average `L0` defines
rounded values `k * L0 / lambda^2`, while the rounded-instance average `LR`
defines the Claim 3.4 and `U`/`V(U)` search window. Do not try to force the
rounded combined supply to have total value `#agents * L0`; use the actual
rounded average `LR`.

Major assumption for completion: Theorem 3.3's final PTAS/FPTAS runtime claim
is intentionally left behind `EconCSLib.Complexity.ExternalSolverConsequence`.
The plan is to finish and review the LMMS04-specific finite proof surface while
discharging the fixed-dimension IP runtime theorem later through a reusable
CSLib/optlib-compatible adapter, not by embedding Lenstra/Kannan machinery in
this paper folder.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Paper definitions: allocation, envy, envy-free, bounded envy, maximum marginal | `paper_is_allocation_of`, `paper_envy`, `paper_envy_free`, `paper_envy_bounded_by`, `paper_max_marginal` | formalized | `LMMS04FairDivision/MainTheorems.lean` | None |
| Lemma 2.2, cycle elimination makes the envy graph acyclic | `paper_lmms_lemma_2_2_acyclic_reduction`, `hasEnvyCycleListExtraction_of_finite` | formalized | `LMMS04FairDivision/MainTheorems.lean`, `EconCSLib/SocialChoice/FairDivision/IndivisibleGoods.lean` | None; finite envy-graph cycle extraction is reusable library support |
| Theorem 2.1, bounded-envy allocation existence | `paper_lmms_theorem_2_1_existence`, `paper_lmms_theorem_2_1_existence_alpha` | formalized with caveat | `LMMS04FairDivision/MainTheorems.lean` | Scope: finite agents/items and monotone finite-good valuation model |
| Theorem 2.1, constructive algorithm correctness | `paper_lmms_algorithm`, `paper_lmms_algorithm_correct`, `paper_lmms_algorithm_correct_list_toFinset` | formalized with caveat | `LMMS04FairDivision/MainTheorems.lean` | Algorithm correctness now states allocation of the input list's `toFinset`; polynomial oracle-time bound not formalized |
| Theorem 2.3, measure-valued utilities with atoms at most `α` | `paper_lmms_theorem_2_3_real_interval_supported_atom_bound`, `theorem2_3_real_interval_supported_atom_bound` | formalized with caveat | `LMMS04FairDivision/MainTheorems.lean`, `LMMS04FairDivision/PaperInterface.lean`, `LMMS04FairDivision/Lemma24MeasurePartition.lean` | Lean states the real-supported interval model explicitly; it splits aggregate point masses above `α / 2`, partitions the residual aggregate measure into finite low-mass pieces, then applies Theorem 2.1 |
| Lemma 2.4, partition `[0,1]` into low-value pieces | `exists_realIntervalPartition_of_singleton_le_half`, `theorem2_3_real_interval_supported_atom_bound` | formalized with caveat | `EconCSLib/Foundations/Probability/RealIntervalPartition.lean`, `LMMS04FairDivision/Lemma24MeasurePartition.lean` | Uses a corrected first-crossing/maximal-cut proof with an `α / 2` residual point-mass guard; this repairs the source prose's "minimum possible value" typo |
| Theorem 3.1, exponential query lower bound for minimum envy/envy-ratio | `paper_lmms_theorem_3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries`, `paper_lmms_theorem_3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries`, `eventually_two_mul_lt_card_of_tendsToZero_ratio`, `paper_lmms_theorem_3_1_hard_function_family_card` | formalized with caveat | `LMMS04FairDivision/Theorem31QueryLowerBound.lean`, `LMMS04FairDivision/Theorem31Counting.lean`, `LMMS04FairDivision/Theorem31QueryTranscript.lean`, `LMMS04FairDivision/Theorem31AdaptiveQuery.lean`, `LMMS04FairDivision/Theorem31Asymptotic.lean`, `LMMS04FairDivision/MainTheorems.lean` | Formalizes the finite hard-function family, transcript-collision core, source swapped-pair obstructions, middle-pair counting assemblies, two-bit query-count cardinal bridge, adaptive deterministic two-bit value-query endpoints, and eventual/asymptotic lower bounds when `2*q/#middle-pairs -> 0`; explicit binomial/exponential growth from the concrete middle layer is not separately formalized |
| Theorem 3.2, Graham 1.4 approximation for envy-ratio | `paper_lmms_theorem_3_2_graham_certificate_to_envy_ratio_bound`, `paper_lmms_theorem_3_2_graham_factor_eq_seven_fifths` | formalized with caveat | `LMMS04FairDivision/Theorem32Graham.lean`, `LMMS04FairDivision/MainTheorems.lean` | The paper cites Graham's scheduling theorem; Lean formalizes the certificate-to-envy-ratio wrapper and the `7 / 5` factor, but not the external scheduling proof |
| Theorem 3.3, PTAS/FPTAS for identical good utilities | `paper_lmms_theorem_3_3_rounded_instance_search_certificate_ratio_guarantee`, `paper_lmms_theorem_3_3_value_pair_search_certificate_size_bound`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_concrete_ip`, `paper_lmms_theorem_3_3_concrete_ip_certificate_of_type_assignment`, `paper_lmms_theorem_3_3_concrete_ip_certificate_of_supply_type_assignment`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_supply_type_assignment`, `paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_rounded_allocation`, `paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_bounded_rounded_allocation`, `paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_bounded_supply_allocation`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_rounded_allocation`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_bounded_rounded_allocation`, `paper_lmms_theorem_3_3_exists_high_good_indexOf`, `paper_lmms_theorem_3_3_exists_low_goods_artificial_supply`, `paper_lmms_theorem_3_3_exists_combined_high_low_rounded_goods_supply`, `paper_lmms_theorem_3_3_exists_combined_high_low_materialized_supply_value_bounds`, `paper_lmms_theorem_3_3_roundedGoodsSupplyOfSupply_eq`, `paper_lmms_theorem_3_3_roundedSupplyValue_pos`, `paper_lmms_theorem_3_3_roundedValue_le_L`, `paper_lmms_theorem_3_3_roundedSupplyValue_le_L`, `paper_lmms_theorem_3_3_roundedValue_lt_L_of_index_lt_top`, `paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_index_lt_top`, `paper_lmms_theorem_3_3_roundedSupplyValue_sum_eq_weighted_supply`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_bounded_supply_allocation`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum`, `paper_lmms_theorem_3_3_roundedModelOfIndex`, `paper_lmms_theorem_3_3_roundedBundleTypeOfBundle_load_eq_sum`, `paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods_weighted_sum_eq_sum_goods`, `paper_lmms_theorem_3_3_isAllocationOf_sum_roundedBundleType_loads_eq_goodsSupply_weighted_sum`, `paper_lmms_theorem_3_3_exact_rounded_allocation_min_max_pair_mem`, `paper_lmms_theorem_3_3_exact_rounded_allocation_types_in_min_max_window`, `paper_lmms_theorem_3_3_roundedBundleTypeOfBundle_mem_min_max_window_of_claim34`, `paper_lmms_theorem_3_3_claim_3_4_min_max_pair_mem_of_rounded_types`, `paper_lmms_theorem_3_3_claim_3_4_value_pair_ip_certificate_of_rounded_types`, `paper_lmms_theorem_3_3_value_pair_search_ratio_le_claim_3_4_min_max`, `paper_lmms_theorem_3_3_search_certificate_ratio_guarantee_and_concrete_ip_summary`, `exists_roundedValueIndex_of_high_good`, `lowGoodsAggregatedSupply_weighted_sum_bounds`, `roundedConcreteIPCertificateOfTypeAssignment`, `roundedInstanceSearchCertificate_ratio_guarantee_and_concrete_ip_summary`, `RoundedConcreteIPCertificate.toValuePairIPCertificate_feasibility_summary`, `RoundedValuePairSearchCertificate.ratio_le_of_concrete_feasible_pair` | partially formalized | `LMMS04FairDivision/Theorem33IdenticalUtilities.lean`, `LMMS04FairDivision/Theorem33RoundedConstruction.lean`, `LMMS04FairDivision/Theorem35RoundingTransfer.lean`, `LMMS04FairDivision/MainTheorems.lean` | Formalizes the finite identical-utilities load model, finite rounded-type/IP certificate seam, finite bounded-type enumeration for the source set `U`, finite value set `V(U)`, source interval slice `U_{u1,u2}`, concrete goods-supply IP equations, rounded goods-supply weighted-value accounting, construction of a concrete IP certificate from an explicit per-agent rounded-type assignment, from a specified rounded supply vector, from an exact rounded-good allocation, from a bounded exact rounded-good allocation using its own rounded min/max load pair, and from a bounded exact materialized-supply allocation using the specified supply vector, high-good source-value-to-index rounding, low-good aggregation into artificial goods of rounded value `L / λ` with the paper's one-unit overshoot bound, the combined high-source/low-artificial rounded goods-supply vector and weighted-value bounds, materialization of any rounded supply vector as finite positive and `L`-bounded rounded items with a strict `< L` criterion for non-top rounded indices and total value equal to the weighted supply vector, materialized combined-supply value bounds, rounded-bundle load equality, finite value-pair search certificate and size bound, the concrete-IP search optimality wrapper, exact-allocation, exact-bounded-allocation, supply-assignment, materialized-supply, and Claim-3.4-on-materialized-supply search optimality, the rounded model induced by a source-good index map, the Claim 3.4 min/max-to-rounded-value-pair bridge, the Claim 3.4 rounded-types value-pair IP constructor, search optimality against a Claim 3.4 min/max IP certificate, bundled final ratio/concrete-IP summary, Lemma 3.5 additive ratio-transfer algebra, and the paper's `λ = 56 / ε` endpoint; still missing a concrete Lenstra/runtime instantiation of the abstract external solver consequence and the final PTAS/FPTAS complexity proof |
| Claim 3.4, bounded optimal allocation under small goods | `paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods`, `paper_lmms_claim_3_4_branch_step_of_exact_nonempty_positive_goods`, `paper_lmms_claim_3_4_exists_bounded_optimal_on_exact_nonempty_positive_goods`, `paper_lmms_claim_3_4_exists_bounded_optimal_of_surjective_owner`, `paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods`, `paper_lmms_exists_nonempty_exact_allocation_of_surjective_owner`, `paper_lmms_claim_3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle`, `paper_lmms_isAllocationOf_moveBundle` | formalized with caveat | `LMMS04FairDivision/Theorem34BoundedOptimal.lean`, `LMMS04FairDivision/Theorem34LocalReallocation.lean`, `LMMS04FairDivision/MainTheorems.lean` | Formalizes the concrete branch step, exact/nonempty-positive finite descent, source-domain finite-search optimizer selection, owner-map construction, and all-goods source wrapper from exact total load plus positive strict-smallness. Scope is finite source goods and exact allocation objects. |
| Lemma 3.5, rounded-instance allocation transfer | `backward_ratio_transfer_of_additive`, `forward_ratio_transfer_of_additive`, `theorem33_ratio_transfer_certificate_epsilon_of_additive`, `theorem33_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads` | partially formalized | `LMMS04FairDivision/Theorem35RoundingTransfer.lean` | Formalizes the arithmetic transfer from raw additive and agentwise additive load inequalities to multiplicative ratio bounds through the paper's `λ = 56 / ε` endpoint; the combinatorial construction of the rounded allocation is still not formalized |
| Theorem 4.1, minimum-envy mechanism not truthful | `paper_lmms_theorem_4_1_source_not_truthful_envy_free_whenever_exists`, `paper_lmms_theorem_4_1_source_minimum_envy_not_truthful`, `lmms41_sourceCounterexampleCertificate` | formalized | `LMMS04FairDivision/MainTheorems.lean`, `LMMS04FairDivision/Theorem41*.lean`, `EconCSLib/SocialChoice/FairDivision/Mechanisms.lean` | None; formalized by a finite two-player/eight-egg source counterexample, with explicit truthful and shifted envy-free witness allocations |
| Theorem 4.2, randomized truthful allocation envy bound | `paper_lmms_theorem_4_2_uniform_random_mechanism_truthful`, `paper_lmms_theorem_4_2_uniform_random_max_envy_probability_bound`, `lmms42_uniformAssignment_maxReportEnvy_prob_ge_of_weights` | formalized | `LMMS04FairDivision/MainTheorems.lean`, `LMMS04FairDivision/Theorem42.lean`, `LMMS04FairDivision/Theorem42Concentration.lean`, `EconCSLib/SocialChoice/FairDivision/Mechanisms.lean` | None; independent uniform random allocation is truthful in expected utility, and the source Chebyshev/union-bound concentration proof is formalized as an explicit finite probability inequality |

The strongest current Theorem 3.3 conditional surface is the public compact
package alias
`theorem3_3_external_solver_selected_pair_full_summary_source_output_package`.
Its verified source-output payload projection is exposed as
`theorem3_3_external_solver_selected_pair_full_summary_source_output_payload`.
Its consequence projection is exposed as
`theorem3_3_external_solver_selected_pair_full_summary_source_output_consequence`.
The scalar and additive Claim-3.4 source-average endpoints
`theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_no_top_of_margin`
and
`theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin`
return that package directly.

## Source-Audit Notes

The cached text contains Theorem 2.1, Lemma 2.2, Theorem 2.3, Lemma 2.4,
Theorems 3.1--3.3, Claim 3.4, Lemma 3.5, and Theorems 4.1--4.2. The current
Lean work covers the finite indivisible-goods core of Theorem 2.1, the named
Lemma 2.2 cycle-elimination wrapper, the real-supported atom-bounded measure
construction for Theorem 2.3, the finite source counterexample for Theorem 4.1,
and the truthful randomized allocation plus concentration proof for Theorem
4.2. Section 3 now has formal support for the Theorem 3.1 hard-family/counting
core, adaptive deterministic two-bit query endpoints, the eventual/asymptotic
query lower-bound wrapper, the Theorem 3.2 source-citation wrapper, Claim 3.4
finite descent from local reallocations, finite identical-utilities load
support, the rounded-type/IP certificate seam, bounded-type enumeration for
the source finite search set, finite value/value-pair search bounds, concrete
source IP goods equations, value-pair search size, concrete-IP optimality, and
finite-search existence wrappers, concrete IP construction from assigned rounded bundle types, exact
rounded-good allocations, and bounded exact rounded-good allocations, rounded
goods-supply weighted accounting, Claim
3.4 min/max rounded-value-pair, value-pair IP, search-optimality, and
search-existence bridges,
bundled final ratio/concrete-IP summary, and Lemma 3.5/Theorem 3.3 additive
ratio-transfer algebra, including high-good source-value-to-index rounding,
low-good aggregation into artificial rounded goods, the combined
high-source/low-artificial rounded goods-supply vector, and a direct concrete-IP
certificate seam for a type assignment over any specified rounded supply.
Materialized rounded supply now also exposes a rounded allocation ratio,
top-index strictness criteria, a bounded-allocation-to-search-existence
wrapper, and no-top Claim-3.4 materialized-supply bridges that discharge the
branch-step premise internally and construct the finite search certificate from
the bounded allocation. The no-top weighted-supply bridge can now construct
the needed owner map internally from exact total value and strict item
smallness, and it also exposes the feasible value-pair/type assignment consumed
by the IP layer. The combined high/low supply now has a no-top support wrapper
under the explicit high-good rounding margin `v_g + L / lambda^2 ≤ L`. The
current source-faithful path is the two-scale rounded-average route: original
`L0` remains the value-grid scale, while the actual rounded average `LR`
supplies the Claim 3.4 and finite-search window. The capped value-pair/IP
search surface is now wired through rounded-supply, combined high/low,
source-average, source-average upper-bound, source-error-bound,
source-error-budget, and auto-cap source-average full-summary ratio endpoints.
The auto-cap path now also has actual-rounded-average endpoints that define
`LR` from the generated combined rounded supply and prove the exact
weighted-average identity internally, including a full-IP summary with explicit
capped search-size bounds. The actual-average source-output package now also has
paired full-IP-summary wrappers for the generic source-average scalar-forward
and additive-forward continuations, alongside the Claim-3.4 specializations.
The rounded-instance search certificate assembly is
now named as
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_transfer`;
the additive variant
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_additive_transfer`
derives those fields from the raw Lemma 3.5 max/min inequalities at
`lambda = 56 / epsilon`, and the agentwise variant
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer`
globalizes per-agent load-transfer estimates to those raw min/max premises.
The bounded-min/max agentwise variant
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_bounded_min_max`
derives the half-average and nonnegativity side conditions from
`Theorem34.boundedAroundAverage`.
The per-agent-window variant
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows`
accepts rounded and optimal allocation-load windows directly and projects them
to the min/max windows required by the transfer algebra. The follow-on
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows_of_backward_min`
derives the output allocation's positive minimum-load premise from the rounded
window and the backward minimum transfer inequality. The Claim-3.4-certificate
variant
`paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_claim34_certificates_of_backward_min`
uses Claim 3.4 certificates as the rounded/optimal window inputs.
The load-function endpoint
`paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads`
composes the same agentwise additive inequalities for source, rounded, and
output load functions that may come from different item types, and
`paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation`
packages that endpoint for concrete source/output and rounded allocations. The
high-good helper
`paper_lmms_theorem_3_3_high_bundle_rounded_load_le_scaled_source_load`
isolates the high-good source-to-rounded bundle-load bound, and
`paper_lmms_theorem_3_3_high_low_bundle_rounded_load_le_forward_transfer`
combines it with a supplied low artificial-load estimate to produce the forward
agentwise additive upper bound. The backward one-bundle helpers
`paper_lmms_theorem_3_3_high_low_bundle_source_load_le_backward_transfer` and
`paper_lmms_theorem_3_3_high_low_bundle_source_load_ge_backward_transfer`
derive the corresponding rounded-to-source upper and lower additive bounds
from supplied low-load estimates; the agentwise wrapper
`paper_lmms_theorem_3_3_backward_agentwise_transfer_of_high_low_bundle_estimates`
packages those two estimates across all agents, while
`paper_lmms_theorem_3_3_forward_agentwise_transfer_of_high_low_bundle_estimates`
packages the forward high/low estimate across agents. The low-good partition boundary
`paper_lmms_theorem_3_3_exists_low_goods_partition_of_owner_load_estimates`
turns an owner map satisfying per-agent low-load estimates into an exact
low-good allocation carrying those estimates, and
`paper_lmms_theorem_3_3_exists_low_partition_and_backward_agentwise_transfer_of_owner_estimates`
combines that exact low allocation with the high/low backward transfer
inequalities. The sibling endpoints
`paper_lmms_theorem_3_3_exists_low_partition_and_forward_agentwise_transfer_of_owner_estimates`,
`paper_lmms_theorem_3_3_exists_low_partition_and_agentwise_transfer_of_owner_estimates`,
and
`paper_lmms_theorem_3_3_exists_low_partition_and_agentwise_transfer_of_owner_estimates_epsilon`
package the forward, two-way, and `lambda = 56 / epsilon` transfer forms. The
four-premise wrapper
`paper_lmms_theorem_3_3_exists_low_partition_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon`
returns the exact backward-max, backward-min, forward-max, and forward-min
agentwise premises consumed by the additive load-transfer endpoint; the
parallel exact-partition variant
`paper_lmms_theorem_3_3_low_partition_agentwise_additive_transfer_premises_epsilon`
uses a supplied exact low-good partition directly. The inverse exact-allocation
helper `paper_lmms_exists_owner_filter_eq_of_isAllocationOf` recovers an owner
map whose filters equal a supplied exact allocation, and
`paper_lmms_exists_low_goods_owner_load_estimates_of_exact_low_partition`
turns exact low-partition estimates into owner-map estimates. The equivalence
`paper_lmms_exists_low_goods_owner_load_estimates_iff_exists_exact_low_partition`
identifies those two low-good target formulations.
The weighted-prefix support
`paper_lmms_exists_prefixWeight_floor`,
`paper_lmms_exists_monotone_prefixWeight_cuts`,
`paper_lmms_prefixSliceWeight_eq_sum_prefixSliceList`, and
`paper_lmms_prefixSliceList_sum_estimates_of_monotone_cuts` proves the ordered
low-good cut skeleton: cumulative targets yield monotone prefix cuts and
concrete slice lists whose loads are within one low-good unit of the target
increments. The `Fin N` specialization
`paper_lmms_exists_prefixSliceList_estimates_for_fin_targets` packages those
slice estimates directly for finite-agent target loads, and
`paper_lmms_exists_prefixSliceList_estimates_for_finite_targets` relabels them
back to an arbitrary finite agent type via the canonical `Fintype.equivFin`
order. The adapter
`paper_lmms_low_goods_owner_load_estimates_of_prefix_sliceList_estimates` turns
represented prefix-slice sums into the owner-filter estimates consumed by the
low-good partition boundary. The conversion from ordered slices to owner
filters is now closed by
`paper_lmms_exists_owner_filter_eq_prefixSliceList_toFinset_of_monotone_cuts`
and `paper_lmms_exists_owner_slice_sum_eq_of_monotone_cuts`, with
`paper_lmms_exists_low_goods_owner_load_estimates_of_finite_prefix_targets`
and its total-sum variant constructing low owner estimates directly from finite
target loads. The corresponding low-partition endpoints
`paper_lmms_theorem_3_3_exists_low_goods_partition_of_finite_prefix_targets`
and
`paper_lmms_theorem_3_3_exists_low_goods_partition_of_finite_prefix_targets_of_total_sum`
construct exact low-good allocations from those targets.
The high/low output assembly helpers
`paper_lmms_isAllocationOf_union_of_disjoint_allocations`,
`paper_lmms_commonLoad_union_eq_add_of_disjoint`,
`paper_lmms_exists_combined_allocation_of_disjoint_exact_allocations`, and
`paper_lmms_exact_high_low_output_assembly` combine exact high and low
allocations over disjoint goods into one exact source allocation with the
expected common-load decomposition. The source-output endpoints
`paper_lmms_theorem_3_3_source_output_allocation_agentwise_additive_transfer_premises_of_exact_low_partition_epsilon`
and
`paper_lmms_theorem_3_3_exists_source_output_allocation_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon`
return that combined output allocation together with the four additive transfer
premises. The ratio wrappers
`paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min`,
`paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min_and_forward_ratio`,
`paper_lmms_theorem_3_3_source_output_ratio_transfer_of_exact_low_partition_epsilon`
and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_owner_estimates_epsilon`
derive output positivity from the rounded window and apply the final epsilon
source-output ratio transfer once the rounded-load identity and forward
optimal-to-rounded estimates are supplied. The scalar-forward variants
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_owner_estimates_forward_ratio_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_forward_ratio_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_forward_ratio_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_forward_ratio_epsilon`, and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_forward_ratio_epsilon`
replace the two pointwise forward premises with the solver-shaped scalar
comparison `roundedRatio <= sourceOptimalRatio * forwardTransferFactor`.
The capped-search bridge now also exposes selected-pair and comparison-IP
variants:
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_ip_forward_additive_epsilon`
derives the scalar comparison from Lemma 3.5 additive pair estimates, and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_comparison_ip_epsilon`
handles the source optimum min/max comparison pair directly. The
`...with_comparison_allocation_forward_ratio_epsilon` and
`...with_comparison_allocation_forward_additive_epsilon` variants construct the
capped comparison IP internally from an exact bounded typed combined comparison
allocation, and the corresponding `...and_search_of_comparison_allocation...`
packages now also construct the capped value-pair search certificate before
deriving source output. The source-min/max finite boundary is also exposed directly:
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_type_assignment`
builds the comparison IP from rounded type witnesses for the bounded source
optimum's min/max loads plus a matching type assignment for the combined
high/low rounded supply. The load/count variant
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_type_assignment_loads_and_counts`
derives capped-window membership and finite min/max type witnesses internally
from a load-realizing source-min/max type assignment and matching rounded-supply
counts; `..._with_larger_cap_of_type_assignment_loads_and_counts` and the
corresponding source-output wrappers lift smaller-cap feasible IPs into the
search cap, while
`..._with_source_auto_cap_of_type_assignment_loads_and_counts` fixes that
comparison IP directly to the paper's source auto-cap. Existential provider
forms expose the same larger-cap and source-auto-cap comparison-IP constructors.
The selected-pair bridge
`paper_lmms_theorem_3_3_selected_pair_forward_ratio_of_larger_cap_source_min_max_comparison_ip_epsilon`
now packages the larger-cap search comparison against the bounded source
optimum's own min/max pair, with a Claim-3.4 companion for certificate-driven
callers.
The corresponding source-output packages now also return that selected-pair
forward-ratio payload alongside the produced larger-cap search certificate and
source output, including the one-scale source-min/max package, the one-scale
Claim-3.4 package, the two-scale Claim-3.4 package, and the two-scale windowed
exact typed allocation route. The same selected-pair payload is preserved by
the two-scale source-min/max windowed type-assignment provider, load/count, and
load/count-provider packages, both at larger caps and at the paper's
source-auto-cap.
Exact typed combined high/low allocations whose rounded loads match
the source optimum now also feed that source-min/max comparison-IP boundary
directly through
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_exact_typed_combined_high_low_allocation_loads`
and its larger-cap and source-auto-cap variants. The two-scale windowed exact
route additionally exposes fixed-cap, larger-cap, and source-auto-cap
comparison IPs, standalone search-only wrappers, provided-search source-output
wrappers, and produced-search packages. The corresponding finite-search and source-output wrappers consume
the same exact typed allocation/load-match premise, including Claim-3.4 entry
points, so this route no longer needs an externally supplied source-min/max
type assignment; an explicit
`...source_min_max_type_assignment_provider_of_exact_typed_combined_high_low_allocation_loads`
theorem also exposes that extracted provider. Package theorems also produce the larger-cap
search certificate internally before deriving the final source output. The same
search/output package is exposed directly for a smaller-cap source-min/max
comparison IP, the current narrow solver-facing boundary, and for the
equivalent source-min/max load/count type-assignment data.
The search-only layer has the same load/count boundary through
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_of_source_min_max_type_assignment_loads_and_counts`.
Provider-shaped source-output wrappers consume the existential form of that
load/count witness directly. Source-auto-cap specializations now fix the
search cap to the paper's canonical `capCountForAverage L (L + extraAverage)
lambda` count for the load/count data route, its provider form, and the exact
typed allocation load-match route, with Claim-3.4 aliases for each.
For actual-average/source-auto-cap solver outputs at scale `L LR`, two-scale
capped-search source-output wrappers now realize the search and, assuming
`L <= LR`, use the realized `boundedAroundAverage LR` rounded window directly
in the source-output transfer.
The source-auto-cap ratio endpoint is also packaged with that bridge; its
remaining solver-facing continuation is the scalar forward bound for the
comparison pair. The actual-rounded-average endpoint has the same package and
defines `LR` internally. Two-scale additive comparison-IP and
comparison-allocation bridges now discharge that scalar comparison from
Lemma 3.5 pair estimates, and the Claim-3.4 source-average and actual-average
facades expose that additive form directly. A two-scale larger-cap package now
also lifts smaller-cap source-min/max comparison IPs into this source-output
route. The selected-pair source-min/max and additive estimates can feed the
two-scale search bridge directly, with matching one-scale wrappers for existing
`L L` search paths. The larger-cap source-min/max source-output packages now
also preserve the selected-pair forward-ratio witness, including the exact
windowed typed allocation route and the source-min/max windowed provider and
load/count routes. The two-scale windowed type-assignment provider facade isolates the
remaining source-min/max feasibility obligation in the actual `L LR` capped
search surface, and its source-auto-cap specialization fixes the resulting
search to the paper's canonical cap. Load-realizing windowed type assignments
now derive the separate source-min/max value-pair membership internally, so the
standalone two-scale comparison IP plus the larger-cap and source-auto-cap
wrappers can consume the natural load/count solver witness directly, including
provider-shaped existential forms and search-only endpoints. The comparison IP itself is now exposed at
the proof cap, at any larger search cap, and at the paper's source auto-cap.
Exact typed high/low allocations with matching source loads now also expose
their induced capped `L LR` type assignment and the corresponding
source-min/max comparison IP. Generated-rounding Claim-3.4 provider wrappers
now choose the combined high/low rounding map internally for both the one-scale
source-auto-cap load/count provider route and the two-scale `L LR` windowed
source-auto-cap route; larger-cap and canonical-cap variants cover separate
search caps and the paper source-auto-cap proof cap, with source-average
larger-cap/canonical variants deriving the rounded lower-bound premises
internally. The same
generated-rounding surface also includes exact typed combined-allocation
provider variants, including source-average canonical wrappers for both the
source-min/max provider route and the exact typed allocation route. These
derive `L ≤ LR` and `0 < LR` from the generated rounded-average identity; the
source-min/max route now also has source-average canonical and larger-cap
selected-pair/full-IP-summary companions exposing the generated comparison IP,
selected-pair forward-ratio payload, and standard bounded summaries alongside
the source output. The larger-cap source-min/max full-summary route carries the
same `largeCap ≤ 2 * lambda + 4` packaging premise. The exact typed route also
has source-auto-cap and larger-cap selected-pair/full-IP companions, in
addition to the earlier full-IP-summary-only endpoints. The canonical exact
typed wrapper derives the `2 * LR` cap condition internally; the larger-cap
full-summary route exposes the extra
`largeCap ≤ 2 * lambda + 4` packaging premise required for bounded summaries.
The solver
auto-cap ratio endpoint now also has a
source-output package that consumes a solver-provided arbitrary feasible pair
under the exact scalar forward-continuation premise, with Claim-3.4 and
additive Lemma-3.5 facades:
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_forward_additive_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin`, and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin`.
The finite-prefix variants
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_epsilon`
and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_total_sum_epsilon`
remove the external low-owner premise by constructing the low owner map from
the ordered low-good prefix construction before applying the same final
source/output transfer. The aggregated-low-load variant
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_epsilon`
derives the finite-prefix total bounds internally from the paper's
`lowGoodsAggregatedSupply` total. The exact low artificial-supply and typed
combined variants
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_aggregated_low_supply_allocation_epsilon`
and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_epsilon`
derive the low total, high source projection, and rounded-load decomposition
from exact allocations of materialized rounded goods. The typed combined seam
also exposes
`paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_bounded_typed_combined_high_low_allocation`,
which packages a bounded exact typed combined allocation as a concrete IP
certificate for the explicit high-source plus low-artificial supply vector;
`paper_lmms_theorem_3_3_exists_typed_combined_high_low_type_assignment_of_exact_bounded_allocation`
and
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_typed_combined_high_low_allocation`
expose the matching type-assignment and finite-search witnesses. The latest
typed endpoint
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_search_of_exact_typed_combined_high_low_allocation_epsilon`
packages the source output and finite-search witness from the same exact typed
allocation, and the typed ratio/concrete-IP search endpoints add the final
rounded-instance `(1 + epsilon)` guarantee.
The capped exact-supply constructor
`paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_supply_allocation`
turns a supplied bounded exact materialized rounded-supply allocation into the
capped concrete IP certificate, and
`paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_typed_combined_high_low_allocation`
does the same for the provenance-carrying typed high/low materialization. Also,
`paper_lmms_theorem_3_3_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`
turns a bounded-allocation provider into the quantified solver premise, and
`paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`
specializes that bridge to the canonical source auto cap. The typed provider
bridge
`paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_typed_combined_high_low_allocation_provider`
now rewrites exact typed high/low allocation providers into the same generated
anonymous-supply solver premise, and the source-average typed variant
`paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider`
derives the rounded-average cap internally from the high/low source-average
hypotheses. The typed workload wrapper
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin`
feeds that premise into the finite source-auto-cap workload summary, while
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin`
adds the final rounded-instance guarantee. The
source-average
variant
`paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_supply_allocation_provider`
derives the needed rounded-average cap from the high/low source-average
hypotheses and the reusable combined-supply bound
`paper_lmms_theorem_3_3_combined_high_low_rounded_goods_supply_weighted_value_bounds`.
The reusable arithmetic is now exposed directly as
`paper_lmms_theorem_3_3_generated_rounded_average_le_source_auto_cap_average_of_source_average`
and
`paper_lmms_theorem_3_3_source_auto_cap_count_satisfies_generated_average_of_source_average`.
The workload wrapper
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
feeds that provider premise directly into the source-auto-cap finite solver
summary, and
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
adds the final rounded-instance guarantee to that same route.
The same source-average provider route now also reaches the solver full-IP
constraint summary, the corresponding full-IP-constraint ratio endpoint, the
full-IP summary ratio endpoint, and the concrete IP/search full-summary ratio
endpoint through
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`, and
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`.
The typed source-average exact-allocation-provider route now reaches the same
finite-workload, full-IP, and concrete IP/search payloads, and the capped
realization endpoints
`paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap`
and
`paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap`
now construct exact bounded anonymous rounded-supply and typed high/low
allocations directly from capped IP certificates, and the search-certificate
variants materialize the chosen capped IP directly. The remaining Section 3
gap is now the external Lenstra/runtime theorem, or an equivalent concrete
machine-model proof, needed to instantiate the abstract solver consequence as
the final PTAS/FPTAS complexity statement. The finite-search size layer now
also exposes explicit
rounded-index cardinality bounds with exponent `lambda^2 + 1`, including
source, two-scale, and source-auto-cap type/value-pair search spaces.
The source-auto-cap solver certificate premise is named as
`paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation`: it asks for a
capped concrete IP certificate at the canonical source-auto cap for every
generated no-top combined high/low rounded supply with rounded total `LR`.
The source-average Claim-3.4 bridge proves this named obligation directly via
`paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_source_average_claim34_no_top_of_margin`.
The main source-auto-cap solver endpoints and source-output solver facades
have `..._of_solver_obligation` wrappers, plus direct source-average
Claim-3.4 discharge wrappers such as
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_ratio_endpoint_of_source_average_claim34_no_top_of_margin`
and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_claim34_solver_obligation_no_top_of_margin`.
The scalar and additive named-obligation source-output routes, their
Claim-3.4-discharge variants, and the corresponding Claim-3.4-certificate
facades also have paired full-IP-summary/source-output wrappers, so callers can
retain the solver full-summary payload next to the verified source allocation
package.
The strongest Claim-3.4-discharge source-output wrapper is
`theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin`,
which packages the selected-pair forward-ratio witness, full IP summaries, the
source-output allocation payload, and the external solver consequence together.
The named obligation can also be constructed from bounded exact
materialized-supply providers or typed high/low allocation providers,
including source-average variants. The conditional
external-complexity seam is exposed through
`paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_consequence`
and its paired obligation-plus-consequence variant. Source-average Claim-3.4
specializations now supply the named obligation internally before applying the
external feasible-solver consequence, and the same external seam now has
source-average exact bounded materialized-supply and typed high/low allocation
provider variants. The external source-output layer also pairs those exact
provider routes with the verified scalar-forward or additive-forward
source-output package, returning the externally supplied consequence alongside
the payload. These wrap an externally supplied feasible solver theorem rather
than proving Lenstra/runtime internally.
Source-output facades now also consume source-average exact bounded
materialized-supply or typed high/low allocation providers directly, with both
scalar-forward and additive-forward continuations, plus Claim-3.4 variants.
The
low-only, strict
high-source, and strict upper-boundary Claim 3.4 moves are now formal
ratio-nonincreasing branch steps, and finite termination is captured by
`paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations`; the
positive-minimum premise is reduced by
`paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations_with_positive_bundles`
and the nonempty-positive-goods wrapper, while
`paper_lmms_claim_3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle`
records that an empty bundle forces zero minimum load under exact allocation of
nonnegative goods; exact `moveBundle` preservation is now isolated as
`paper_lmms_isAllocationOf_moveBundle`. The strengthened exact branch-step
surface is `paper_lmms_claim_3_4_branch_step_of_exact_nonempty_positive_goods`,
and the hstep-free exact wrapper is
`paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods`.
The source-domain selector endpoints are
`paper_lmms_exists_nonempty_exact_allocation_of_surjective_owner`,
`paper_lmms_exists_surjective_owner_of_total_strictly_small_positive_values`,
`paper_lmms_claim_3_4_exists_bounded_optimal_on_exact_nonempty_positive_goods`,
`paper_lmms_claim_3_4_exists_bounded_optimal_of_surjective_owner`, and
`paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods`.

Recent Theorem 3.3 finite-search existence endpoints are
`exists_roundedValuePairSearchCertificate_of_feasible_pair`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_concrete_ip`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_supply_type_assignment`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_supply_allocation`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_claim_3_4_min_max`,
`paper_lmms_theorem_3_3_exists_supply_type_assignment_of_exact_bounded_supply_allocation`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_exact_supply_optimum_no_top`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_exact_supply_optimum_no_top_of_weighted_supply`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_owner_no_top_of_weighted_supply`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_no_top_of_weighted_supply`,
`paper_lmms_theorem_3_3_exists_value_pair_type_assignment_of_claim34_no_top_weighted_supply`,
`paper_lmms_theorem_3_3_exists_value_pair_type_assignment_of_combined_high_low_claim34_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_of_claim34_no_top_of_margin`,
and
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_combined_high_low_type_assignment`.
The no-top materialized Claim-3.4 bridge is
`paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top`;
its weighted-supply-average form is
`paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top_of_weighted_supply`.
The combined-supply no-top support endpoint is
`paper_lmms_theorem_3_3_exists_combined_high_low_rounded_goods_supply_no_top_of_margin`.
The current two-scale endpoints are
`Theorem33.roundedAdmissibleTypeSetWithCap`,
`Theorem33.RoundedConcreteIPCertificateWithCap`,
`Theorem33.RoundedValuePairSearchCertificateWithCap`,
`Theorem33.exists_roundedValuePairSearchCertificateWithCap_of_feasible_pair`,
`paper_lmms_claim_3_4_exists_bounded_optimal_for_rounded_supply_average_no_top`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_error_bound_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_error_budget_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_value_pair_search_certificate_with_auto_cap_materialized_full_summary_ratio_guarantee_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_auto_cap_full_ip_summary_with_ratio_guarantee_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_auto_cap_full_ip_summary_of_additive_transfer_no_top_of_margin`,
`paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_supply_allocation`,
`paper_lmms_theorem_3_3_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`,
`paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_supply_allocation_provider`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_forward_additive_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon`,
`paper_lmms_theorem_3_3_source_min_max_pair_mem_roundedAdmissibleValuePairSetWithCap_of_windowed_type_assignment_loads`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_windowed_type_assignment_loads_and_counts`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_type_assignment_loads_and_counts`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_type_assignment_loads_and_counts_provider`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_type_assignment_loads_and_counts`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_type_assignment_loads_and_counts_provider`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_type_assignment_loads_and_counts`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_type_assignment_loads_and_counts_provider`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_type_assignment_loads_and_counts`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_type_assignment_loads_and_counts_provider`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_larger_cap_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_larger_cap_provider_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_source_auto_cap_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_source_auto_cap_provider_epsilon`,
`paper_lmms_theorem_3_3_exists_typed_combined_high_low_type_assignment_with_cap_loads_of_exact_bounded_allocation`,
`paper_lmms_theorem_3_3_source_min_max_windowed_type_assignment_provider_of_exact_typed_combined_high_low_allocation_loads`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_windowed_exact_typed_combined_high_low_allocation_loads`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_exact_typed_combined_high_low_allocation_loads`,
`paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_exact_typed_combined_high_low_allocation_loads`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_exact_typed_combined_high_low_allocation_loads`,
`paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_exact_typed_combined_high_low_allocation_loads`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_source_auto_cap_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon`,
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon`,
and
`paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin`.
