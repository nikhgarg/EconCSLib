# LMMS04 Next-Agent Startup

Current stopping point: 2026-05-26.

Start with the concise transition plan, then use the full handoff for details:

- `papers/LMMS04FairDivision/TRANSITION_PLAN_2026-05-26.md`
- `papers/LMMS04FairDivision/HANDOFF_2026-05-25.md`

## Validation Status

Latest targeted checks in this stopping-point pass:

```bash
lake env lean papers/LMMS04FairDivision/Theorem33RoundedConstruction.lean
lake env lean papers/LMMS04FairDivision/MainTheorems.lean
lake build LMMS04FairDivision
lake env lean -t 0 papers/LMMS04FairDivision/PaperInterface.lean
lake env lean -t 0 papers/LMMS04FairDivision/MainTheorems.lean
rg -n '\b(sorry|admit|axiom|opaque|placeholder|TODO|FIXME)\b' papers/LMMS04FairDivision --glob '*.lean'
python3 /home/nkgarg/.codex/skills/.system/skill-creator/scripts/quick_validate.py skills/econcs-formalizer
```

Before continuing after new edits, rerun:

```bash
lake build LMMS04FairDivision
```

The review dashboard cache has been refreshed. `./review-dashboard.sh --check`
currently reports `0/791` reviewed, `0` stale, and `0` mismatch; the nonzero
exit is only because no human review entries have been saved.

## Active Seam

Theorem 3.3 is on the rounded-instance finite-search bridge. The verified
full-summary capped-search endpoints still use two different scales:

- `L0`: original instance average, used for values `k * L0 / lambda^2`.
- `LR`: rounded-instance average, used in Claim 3.4 and the `U`/`V(U)` search
  window.

Do not try to prove that the rounded combined supply has total value
`#agents * L0`. The faithful route is to define/use the actual rounded average
`LR` from the weighted rounded supply total.

## Strongest New Endpoints

- `Theorem33.roundedAdmissibleTypeSetWithCap`
- `Theorem33.RoundedConcreteIPCertificateWithCap`
- `Theorem33.RoundedValuePairSearchCertificateWithCap`
- `Theorem33.exists_roundedValuePairSearchCertificateWithCap_of_feasible_pair`
- `paper_lmms_claim_3_4_exists_bounded_optimal_for_rounded_supply_average_no_top`
- `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top`
- `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_error_bound_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_error_budget_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_materialized_full_summary_ratio_guarantee_of_source_average_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_value_pair_search_certificate_with_auto_cap_materialized_full_summary_ratio_guarantee_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_auto_cap_full_ip_summary_with_ratio_guarantee_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_auto_cap_full_ip_summary_of_additive_transfer_no_top_of_margin`
- `paper_lmms_theorem_3_3_combined_high_low_rounded_goods_supply_weighted_value_bounds`
- `paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_supply_allocation`
- `paper_lmms_theorem_3_3_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`
- `paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`
- `paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_supply_allocation_provider`
- `paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
- `paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
- `paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_transfer`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_additive_transfer`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_bounded_min_max`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows_of_backward_min`
- `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_claim34_certificates_of_backward_min`
- `paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads`
- `paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation`
- `paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min`
- `paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min_and_forward_ratio`
- `paper_lmms_theorem_3_3_source_output_ratio_transfer_of_exact_low_partition_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_owner_estimates_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_owner_estimates_forward_ratio_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_forward_ratio_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_forward_ratio_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_forward_ratio_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_forward_ratio_epsilon`
- `paper_lmms_theorem_3_3_high_bundle_rounded_load_le_scaled_source_load`
- `paper_lmms_theorem_3_3_high_low_bundle_rounded_load_le_forward_transfer`
- `paper_lmms_theorem_3_3_high_low_bundle_source_load_le_backward_transfer`
- `paper_lmms_theorem_3_3_high_low_bundle_source_load_ge_backward_transfer`
- `paper_lmms_theorem_3_3_backward_agentwise_transfer_of_high_low_bundle_estimates`
- `paper_lmms_theorem_3_3_exists_low_goods_partition_of_owner_load_estimates`
- `paper_lmms_theorem_3_3_exists_low_partition_and_backward_agentwise_transfer_of_owner_estimates`
- `paper_lmms_isAllocationOf_filter_owner`
- `paper_lmms_exists_prefixWeight_floor`
- `paper_lmms_exists_monotone_prefixWeight_cuts`
- `paper_lmms_prefixSliceWeight_eq_sum_prefixSliceList`
- `paper_lmms_prefixSliceList_sum_estimates_of_monotone_cuts`
- `paper_lmms_exists_prefixSliceList_estimates_for_fin_targets`
- `paper_lmms_exists_prefixSliceList_estimates_for_finite_targets`
- `paper_lmms_low_goods_owner_load_estimates_of_prefix_sliceList_estimates`
- `paper_lmms_isAllocationOf_union_of_disjoint_allocations`
- `paper_lmms_exact_high_low_output_assembly`
- `paper_lmms_theorem_3_3_source_output_allocation_agentwise_additive_transfer_premises_of_exact_low_partition_epsilon`
- `paper_lmms_theorem_3_3_exists_source_output_allocation_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon`
- `theorem3_3_external_solver_selected_pair_full_summary_source_output_package`
- `theorem3_3_external_solver_selected_pair_full_summary_source_output_payload`
- `theorem3_3_external_solver_selected_pair_full_summary_source_output_consequence`
- `theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_no_top_of_margin`
- `theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin`

## Next Step

Continue from the verified full-summary capped-search layer. The auto-cap path
now has actual-rounded-average endpoints that define `LR` from the generated
combined supply and prove the exact weighted-average identity internally. The
source-average exact-allocation-provider route now also feeds the finite solver
workload summary, solver full-IP summaries, concrete IP/search full summary,
and their ratio endpoints. The transfer boundary now derives the output
positive-minimum premise from the rounded allocation window and backward minimum
transfer inequality, accepts Claim-3.4 certificates for the rounded/optimal
windows, and has a load-function endpoint for source/rounded/output loads on
different item types, plus a concrete source-output/rounded-allocation wrapper.
The high-good source-to-rounded bundle-load bound, the high/low forward and
backward transfer helpers under supplied low artificial-load estimates, and the
agentwise forward/backward transfer packaging plus owner-filter
exact-allocation helper are isolated. The low-good partition boundary now
reduces that construction to finding an owner map satisfying the per-agent
low-load estimates, and the combined endpoints package the resulting exact low
allocation with forward, backward, two-way, and `lambda = 56 / epsilon`
agentwise transfer inequalities, including a four-premise wrapper in the exact
shape consumed by the additive load-transfer endpoint. There is also a
matching exact-low-partition variant that does not require the owner map once
the low partition is supplied directly. Conversely,
`paper_lmms_exists_owner_filter_eq_of_isAllocationOf` recovers an owner map
from any exact allocation, and
`paper_lmms_exists_low_goods_owner_load_estimates_of_exact_low_partition`
turns exact low-partition estimates into owner-load estimates; the iff theorem
`paper_lmms_exists_low_goods_owner_load_estimates_iff_exists_exact_low_partition`
shows these are equivalent target formulations. Exact high/low output assembly
now unions the high and low allocations over disjoint goods and returns the
combined source output allocation with the four additive transfer premises. The
source-output ratio wrapper derives output positivity from the rounded window and
backward-minimum transfer. The exact-low-partition and owner-estimate routes
still support the original pointwise forward premises, and the newer scalar
forward-ratio route now matches solver certificates that prove only
`roundedRatio <= sourceOptimalRatio * forwardTransferFactor (56 / epsilon)`.
The weighted-prefix support now proves maximal prefix floors, monotone
cumulative cuts, concrete prefix-slice lists, per-slice one-unit estimates, and
a `Fin N` plus arbitrary finite-agent target specialization; represented
prefix-slice sums now feed a verified slice-to-owner construction, finite-prefix
owner-load estimates, exact low partitions, and finite-prefix source-output
ratio endpoints. The aggregated-low-load source-output endpoint also derives
the finite-prefix low-total bounds from `lowGoodsAggregatedSupply`. Exact
materialized low-supply allocations now supply that aggregate total directly,
and the provenance-carrying typed combined high/low materialization projects an
exact rounded allocation into the high source allocation, low rounded loads,
rounded-load decomposition, source-output ratio endpoint, and concrete IP
certificate for the explicit high-plus-low supply vector. It now also carries
the finite-search witness, final ratio-guarantee search/IP endpoints, a capped
concrete-IP constructor, a typed-provider-to-source-auto-cap solver premise, and
a source-average typed-provider variant that derives the rounded-average cap
internally, typed-provider finite-workload, full-IP, and concrete IP/search
summary endpoints, plus a source-output-plus-search endpoint. The capped
concrete-IP realization layer now constructs exact bounded anonymous
rounded-supply and typed high/low allocations directly from capped IP
certificates, including the chosen capped IP in a value-pair search
certificate. The source-output layer now has capped selected-pair and
comparison-IP variants, including a source-min/max comparison-pair route that
removes the separate scalar forward-ratio premise once that capped comparison
IP is available; a typed comparison-allocation route now builds the capped
comparison IP internally from an exact bounded typed combined allocation,
using either a scalar forward-ratio premise or additive pair estimates, and now
also has packages that internally produce the capped search certificate before
deriving source output. The
source-min/max route also has a direct type-assignment constructor for the
capped comparison IP, cap monotonicity/lift lemmas, larger-cap search
existence from smaller-cap feasible IPs, and load/count variants that derive
the source-min/max capped-window membership and finite min/max rounded type
witnesses internally; the same load/count data now also has a direct
source-auto-cap comparison-IP constructor, with provider-shaped variants for
larger-cap and source-auto-cap comparison IPs. The typed combined high/low extraction now returns the
per-agent rounded-load identity for its induced type assignment, and exact typed
combined allocations with matching source loads can now construct the
source-min/max capped comparison IP at either the proof cap or a larger search
cap, and at the canonical source auto-cap; it also exposes the corresponding
source-min/max load/count provider as a standalone theorem. The same exact-allocation/load-match premise now also feeds the larger-cap
finite-search certificate and capped-search source-output wrappers, including
Claim-3.4 variants, and package theorems now produce the larger-cap search
certificate internally before deriving source output. There is also a direct
search/output package from a smaller-cap source-min/max comparison IP, which is
the narrowest current solver-facing boundary, plus the equivalent package from
source-min/max load/count type-assignment data and an existential provider
variant of that witness. The load/count data route, its provider form, and the
exact typed allocation/load-match route also have source-auto-cap
specializations at
`capCountForAverage L (L + extraAverage) lambda`, with Claim-3.4 variants. The
two-scale actual-average solver path now has wrappers that realize an `L LR`
capped search and, assuming `L <= LR`, use the realized
`boundedAroundAverage LR` rounded window directly in the source-output transfer.
The lightweight source-auto-cap ratio endpoint now has a source-output package
whose remaining solver-facing continuation is the scalar forward bound for the
comparison pair; the actual-rounded-average endpoint has the same package and
defines `LR` internally. The newest pass adds two-scale additive comparison-IP
and comparison-allocation bridges, Claim-3.4 scalar value-pair wrappers, an
admissible-value-pair positivity helper, and source-average plus actual-average
additive facades that discharge the packages' scalar continuations from
Lemma 3.5 max/min pair estimates. The solver auto-cap ratio endpoint now also
feeds the source-output bridge directly when supplied the scalar forward
comparison for the solver's arbitrary feasible pair:
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_no_top_of_margin`.
The generic additive-forward forms are
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_no_top_of_margin`
and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_forward_additive_no_top_of_margin`.
The Claim-3.4 and Claim-3.4 additive forms are
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin`
and
`paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin`.
It also has a two-scale larger-cap package
from a smaller-cap source-min/max comparison IP, plus selected-pair source-min/max
and additive variants for one-scale and two-scale searches. The selected-pair
forward-ratio payload is now preserved by the source-output packages for the
one-scale source-min/max route, the one-scale and two-scale Claim-3.4 routes,
the two-scale windowed exact typed allocation route, and the source-min/max
windowed provider/load-count routes. The explicit two-scale windowed
type-assignment provider facade is also available; it is the cleanest boundary
for proving source min/max feasibility in the `L LR` capped search surface, and
its source-auto-cap specialization fixes the resulting search to the paper's
canonical cap. Load-realizing windowed type assignments now derive the separate
source-min/max value-pair membership internally, giving a standalone two-scale
comparison IP at the proof cap, larger-cap and source-auto-cap comparison-IP
constructors, source-output wrappers over the direct load/count witness, and
search-only/provider variants for existential solver output. Generated-rounding
Claim-3.4 provider wrappers now choose the combined high/low rounding map
internally for both the one-scale and two-scale source-auto-cap source-min/max
provider routes, with larger-cap and canonical-cap variants for the two-scale
provider surface. The source-min/max provider route now also has a
source-average larger-cap wrapper and a source-average canonical wrapper
deriving `L ≤ LR` and `0 < LR` internally. The canonical source-average route
also has a full-IP-summary companion exposing the generated source-min/max
comparison IP and standard bounded summary facts alongside the source output;
the source-average larger-cap route now has the analogous full-IP-summary
companion at `largeCap`, assuming `largeCap ≤ 2 * lambda + 4`.
Exact typed allocation provider variants include source-average canonical and
larger-search-cap wrappers. The exact typed generated/provider route now also
has selected-pair-plus-full-IP companions for the source-auto-cap and larger-cap
endpoints, alongside the older full-IP-summary-only wrappers. The canonical
source-average route derives `L ≤ LR`, `0 < LR`, and the `2 * LR` cap
internally; the larger-cap full-summary companion carries the required
`largeCap ≤ 2 * lambda + 4` bounded-summary premise.
Exact typed high/low allocations with matching source loads now expose the
induced capped `L LR` type-assignment witness and fixed-cap, larger-cap, and source-auto-cap
source-min/max comparison IPs directly, plus two-scale search-only,
provided-search, and produced-search source-output packages. The finite-search
cardinality layer now has explicit `lambda^2 + 1` rounded-index exponent
bounds for the source, two-scale, and source-auto-cap type/value-pair search
spaces. The source-auto-cap solver certificate premise is named
`paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation`; it is a
certificate obligation, not a runtime theorem. Provider constructors now derive
that named obligation from bounded exact materialized-supply providers and
typed high/low allocation providers, including the source-average variants
that prove the cap bound internally. The source-average Claim-3.4 theorem
`paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_source_average_claim34_no_top_of_margin`
now discharges the certificate side of that obligation directly from the
rounded-supply bridge, and the source-average external-complexity wrappers
route that discharge into an externally supplied feasible-solver consequence.
The reusable source-auto-cap arithmetic now also exposes generated
rounded-average and generated-cap-count helpers for any generated rounded
supply with exact weighted average `LR`. The corresponding public
`..._of_solver_obligation` aliases now feed that named premise into the
workload, full-IP-constraint, full-IP-summary, concrete-IP/search summary, and
compact ratio endpoints. The source-output solver facades also have
`...source_average...of_solver_obligation...` and
`...claim_3_4_source_average...of_solver_obligation...` variants, including the
additive-forward forms. The scalar/additive named-obligation facades, their
Claim-3.4-discharge variants, and the corresponding Claim-3.4-certificate
facades also have paired full-IP-summary/source-output companions, and the
actual-average source-output route has paired full-IP-summary wrappers for the
generic source-average scalar-forward and additive-forward continuations. There are also
direct source-output provider facades for source-average exact bounded
materialized-supply and typed high/low allocation
providers, in both scalar-forward and additive-forward forms. The external
source-output provider variants pair those exact-provider scalar and additive
facades with an externally supplied feasible-solver consequence. The
source-average Claim-3.4 discharge is now wired directly through the lower
solver summaries and source-output facades, including the scalar and additive
Claim-3.4 bounded-optimum variants, selected-pair forward-ratio witnesses, and
full-IP-summary/source-output packages. The
complexity seam now uses
`EconCSLib.Complexity.ExternalSolverConsequence` through
`paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_consequence`
and the paired
`paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_and_consequence`;
there are also source-average exact bounded materialized-supply and typed
high/low allocation provider variants of that external seam. These are
conditional wrappers, not runtime proofs. The source-output provider wrappers
also expose paired payload-plus-consequence endpoints for those exact-provider
routes, and the additive Claim-3.4 source-average route now has the combined
selected-pair/full-summary/source-output/external-consequence endpoint
`theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin`.
The next useful Section 3 work is proving or importing the concrete
Lenstra/runtime certificate and packaging the final PTAS/FPTAS complexity
statement.
