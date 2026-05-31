# LMMS04 Formalization Plan

Last updated: 2026-05-26

## Current State

- `PaperInterface.lean` exposes the finite indivisible-goods Theorem 2.1 review
  surface, Lemma 2.2, Theorem 2.3's real-supported atom-bounded measure
  construction, the active Section 3 rounded-search/Claim-3.4 interface, and
  Section 4 mechanism/truthfulness support.
- `MainTheorems.lean` keeps the proof-facing wrappers and the algorithmic
  correctness statement.
- `Theorem41*.lean` contains the finite two-player/eight-egg source model,
  case split, witness allocations, and mechanism-level counterexample for
  Theorem 4.1.
- `Theorem42.lean` and `Theorem42Concentration.lean` contain the uniform random
  mechanism, deterministic `f_{pq}` envy identity, moment calculation,
  Chebyshev tail, and finite union-bound proof for Theorem 4.2.
- The measurable partition construction is closed for the real-supported
  interval model.
- Section 3 now has compiling support for the Theorem 3.1 finite hard-family
  lower-bound route, including adaptive deterministic two-bit value-query
  endpoints derived from `2 * q < #middle-pairs` and eventual/asymptotic
  wrappers from `2*q/#middle-pairs -> 0`.
- Claim 3.4 now has a finite-descent assembly from the source high-bundle move
  into any bundle of load at most `L`, using the global
  `overfullBundleCardPotential`; the complementary low-only case has the
  positive max-to-min small-item lemma, ratio-nonincreasing local move
  certificate, no-high primary-potential preservation, finite min-load
  tie-potential descent, domain-restricted lexicographic finite descent over an
  explicit feasible set plus exact positive-minimum, concrete-potential, exact
  nonempty-positive, and concrete-potential nonempty-positive source-domain
  allocation wrappers, the min/max source-branch constructor, and the
  lexicographic high-source/low-only branch assembly endpoint. The source
  trichotomy theorem now discharges the strict high-source, low-only, and
  strict upper-boundary cases; the paper-facing Claim 3.4 row is now an
  exact finite-allocation wrapper where `IsAllocationOf` supplies ownership,
  item-domain, average-load, exact `moveBundle` preservation, and move-update
  plumbing. The exact nonempty positive-goods branch step is now discharged by
  `paper_lmms_claim_3_4_branch_step_of_exact_nonempty_positive_goods`, and the
  hstep-free wrapper
  `paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods`
  returns a bounded exact optimum from a nonempty exact starting optimum when
  total load is `#agents * L` and all goods are positive and strictly below
  `L`. The source-domain selector
  `paper_lmms_claim_3_4_exists_bounded_optimal_on_exact_nonempty_positive_goods`
  now chooses such an optimum from any nonempty exact feasible domain, and
  `paper_lmms_claim_3_4_exists_bounded_optimal_of_surjective_owner` supplies
  that domain from an owner map that gives every agent at least one good. A
  separate obstruction lemma shows that an exact allocation with an empty
  bundle and nonnegative goods has minimum load zero. The finite all-goods
  wrapper
  `paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods`
  now instantiates the owner/average/small-good premises for exact source
  goods with positive values, strict smallness, and total load `#agents * L`.
- Theorem 3.3 has the rounded-type/IP certificate seam, finite bounded-type
  enumeration for the source set `U`, finite value set `V(U)`, value-pair
  search bound, source interval slice `U_{u1,u2}`, concrete goods-supply IP
  equations, rounded goods-supply weighted-value accounting, concrete IP
  certificate construction from explicit per-agent rounded-type assignments,
  exact rounded-good allocations, and bounded exact rounded-good allocations
  using their own rounded min/max load pair, rounded-bundle load equality,
  finite value-pair search certificate and size bound, the concrete-IP search
  optimality wrapper, exact-allocation and exact-bounded-allocation search
  optimality, high-good source-value-to-index rounding, low-good aggregation
  into artificial rounded goods with the paper's one-unit overshoot bound, the
  rounded model induced by a source-good index map, the Claim 3.4 min/max
  rounded-value-pair bridge, Claim 3.4 rounded-types value-pair IP constructor,
  search optimality against a Claim 3.4 min/max IP certificate, finite-search
  existence from concrete IP certificates and from Claim 3.4 min/max IP
  certificates, bundled final ratio/concrete-IP summary, Lemma 3.5 additive
  transfer algebra, agentwise additive-transfer globalization with a
  bounded-min/max Claim-3.4-window variant, and the
  combined high-source/low-artificial rounded goods-supply vector closed.
  The concrete-IP seam now also accepts an externally specified rounded supply
  vector through a per-agent rounded-type assignment and materializes any
  supply vector as finite positive and `L`-bounded rounded items with a strict
  `< L` criterion for non-top rounded indices and total value equal to the
  weighted supply vector. The combined high/low supply now has matching
  materialized-item value bounds, bounded exact materialized-supply allocations
  produce standalone concrete-IP certificates and finite-search existence
  wrappers for the specified supply, and the value-pair search comparison can
  be routed through Claim 3.4 on the materialized supply. The no-top
  materialized bridge
  `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top`
  removes the raw Claim 3.4 branch-step premise when the materialized supply
  has no top-index items and total value exactly `#agents * L`; the companion
  `paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top_of_weighted_supply`
  states the average premise as the weighted rounded-supply sum. The matching
  existence wrappers now build the finite value-pair search certificate from
  the bounded Claim 3.4 allocation, and
  `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_combined_high_low_type_assignment`
  isolates the remaining combined-supply solver certificate. The no-top
  weighted-supply bridge now constructs the owner map internally from exact
  total value plus strict item smallness and exposes the resulting feasible
  value-pair/type assignment through
  `paper_lmms_theorem_3_3_exists_value_pair_type_assignment_of_claim34_no_top_weighted_supply`.
  For the combined high/low supply,
  `paper_lmms_theorem_3_3_exists_combined_high_low_rounded_goods_supply_no_top_of_margin`
  proves top-index support is zero under the explicit high-good rounding
  margin `v_g + L / lambda^2 ≤ L`. The source-faithful route now separates the
  original average `L0`, used for rounded values `k * L0 / lambda^2`, from the
  rounded-instance average `LR`, used for Claim 3.4 and the finite `U`/`V(U)`
  search window. `Theorem33RoundedConstruction.lean` now exposes the capped
  two-scale search surface `roundedAdmissibleTypeSetWithCap`,
  `RoundedConcreteIPCertificateWithCap`,
  `RoundedValuePairSearchCertificateWithCap`, and
  `exists_roundedValuePairSearchCertificateWithCap_of_feasible_pair`.
  `MainTheorems.lean` exposes
  `paper_lmms_claim_3_4_exists_bounded_optimal_for_rounded_supply_average_no_top`
  for materialized rounded values at scale `L0` and Claim 3.4 window `LR`.
  The older `...combined_high_low...claim34_no_top...` wrappers remain useful
  stronger staging endpoints, but they should not be treated as the final paper
  path unless an explicit one-scale normalization theorem is proved. The capped
  two-scale IP/search layer is now wired through full-summary rounded-supply,
  combined high/low, source-average, source-error, and auto-cap ratio
  endpoints. The auto-cap route now also has actual-rounded-average wrappers
  that define `LR` from the generated combined supply and prove the exact
  weighted-average identity internally, plus a source-auto-cap solver-premise
  adapter from exact bounded materialized-supply allocation providers. A
  source-average version derives the rounded-average cap bound internally from
  a reusable combined high/low weighted-value bound, and the matching workload
  wrapper routes that provider directly into the finite source-auto-cap solver
  summary and rounded-instance ratio endpoint. The same source-average
  provider route now also exposes the solver full-IP constraint summary,
  full-IP-constraint ratio endpoint, full-IP summary ratio endpoint, and
  concrete IP/search full-summary ratio endpoint, via the four
  `...source_average_exact_bounded_supply_allocation_provider...` solver
  full-IP wrappers in `MainTheorems.lean` and public aliases in
  `PaperInterface.lean`; the corresponding typed-provider route now reaches
  the same full-IP and concrete-search payloads. The actual-rounded-average
  route now also has paired full-IP-summary/source-output wrappers for the
  generic source-average scalar-forward and additive-forward continuations, as
  well as the Claim-3.4 specializations. The capped concrete-IP
  realization layer now includes the type-slot assignment theorem, the indexed
  item-slot matching theorem, and the full anonymous-supply and typed high/low
  realization endpoints
  `paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap`
  and
  `paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap`;
  the corresponding search-certificate wrappers materialize the chosen capped
  IP directly.
  The
  rounded-instance search certificate
  assembly is now named by
  `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_transfer`,
  and
  `paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_additive_transfer`
  derives its transfer fields from the raw Lemma 3.5 max/min additive
  inequalities. The per-agent-window transfer wrapper now projects rounded and
  optimal allocation-load windows to the min/max transfer side conditions, and
  the backward-min variant derives the output positive-minimum premise from the
  rounded window plus the backward minimum transfer estimate. A Claim-3.4
  certificate variant now consumes the rounded and optimal Claim-3.4
  certificates directly, while the load-function transfer endpoint composes
  agentwise additive inequalities across source, rounded, and output load
  functions with different item types; the concrete source-output/rounded
  allocation wrapper packages that result with exact source-output allocation.
  The high-good bundle-transfer helper now proves the source-to-rounded
  high-good load scaling bound, the high/low forward-transfer helper combines
  that with a supplied low artificial-load estimate, the high/low backward
  transfer helpers derive the rounded-to-source upper and lower bundle bounds
  from supplied low-load estimates, the agentwise forward/backward transfer
  wrappers package those estimates across all agents, the low-good owner-map
  boundary builds an exact low-good allocation from per-agent low-load
  estimates, the combined low-partition endpoints package that allocation with
  forward, backward, two-way, and `lambda = 56 / epsilon` agentwise transfer
  inequalities, including a four-premise endpoint in the exact shape consumed
  by the additive load-transfer API, the exact-low-partition variant exposes
  the same four premises without going through an owner map, the
  exact-allocation-to-owner helper recovers owner filters from any exact
  allocation and turns exact low-partition estimates into owner-load estimates,
  the low-owner/low-partition iff identifies those target formulations, the
  high/low source-output assembly helpers union exact high and low allocations
  over disjoint goods and expose the common-load decomposition, the
  source-output endpoints return the combined output allocation with the four
  additive transfer premises, the weighted-prefix construction now turns
  monotone ordered low-good slices into owner-filter bundles and finite-prefix
  target low partitions, and the finite-prefix source-output endpoints remove
  the external low-owner premise before applying the final epsilon transfer.
  Exact allocations of the materialized low artificial supply now provide the
  low total internally, and exact allocations of the provenance-carrying typed
  combined high/low supply project to exact high source allocations, extracted
  low loads, rounded-load decompositions, source-output ratio transfer, and a
  concrete IP certificate for the explicit high-plus-low supply vector. They
  now also expose type-assignment, finite-search, ratio-guarantee, capped-IP,
  typed-provider solver-premise, and source-output-plus-search endpoints. The
  scalar-forward source-output variants now replace the two pointwise forward
  premises with a solver-shaped rounded-vs-source-optimum ratio comparison, and
  the capped comparison-IP variants discharge that scalar premise from additive
  pair estimates or the source optimum min/max pair. A typed comparison
  allocation wrapper now builds the capped comparison IP internally from an
  exact bounded typed combined allocation, with either a scalar forward-ratio
  premise or additive pair estimates, and package wrappers now produce the
  capped search certificate internally before deriving source output. The
  source-min/max route also has a
  direct type-assignment constructor for the capped comparison IP, plus
  load/count variants that derive capped-window membership and min/max rounded
  type witnesses internally, including a direct constructor at the canonical
  source auto-cap and provider-shaped comparison-IP constructors. Cap monotonicity now lifts feasible concrete IPs
  into larger search caps, including exact typed combined allocations whose
  rounded loads match the source optimum; that exact typed-allocation route
  now also constructs the source-min/max comparison IP at the source auto-cap
  and exposes the source-min/max load/count provider directly. The two-scale
  windowed exact route now also exposes fixed-cap, larger-cap, and
  source-auto-cap comparison IPs, standalone search-only wrappers,
  provided-search source-output wrappers, and produced-search packages,
  including Claim-3.4 specializations. Package
  theorems now produce the larger-cap search certificate internally before
  deriving source output. A
  direct search/output package from a smaller-cap source-min/max comparison IP
  is now the narrowest current solver-facing boundary, with an equivalent
  package for source-min/max load/count type-assignment data and an existential
  provider version of that witness. Source-auto-cap specializations at
  `capCountForAverage L (L + extraAverage) lambda` are now available for the
  load/count data route, its provider form, and the exact typed
  allocation/load-match route, including Claim-3.4 entry points. The
  actual-average solver path is explicitly two-scale: capped-search wrappers
  now realize an `L LR` search and, assuming `L <= LR`, use the
  `boundedAroundAverage LR` certificate directly in the source-output transfer.
  The lightweight source-auto-cap ratio endpoint is now also packaged with
  that two-scale source-output bridge, leaving only the scalar forward bound
  for the comparison pair as its solver-facing continuation.
  The actual-rounded-average auto-cap endpoint has the same source-output
  package while existentially defining `LR` internally. Two-scale additive
  comparison-IP and comparison-allocation bridges now discharge the scalar
  comparison from Lemma 3.5 pair estimates, and the Claim-3.4 source-average
  and actual-average facades package those additive estimates as the
  source-output continuations. The solver auto-cap ratio endpoint now also
  reaches the source-output bridge under the same scalar-forward discipline:
  `paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_no_top_of_margin`,
  plus generic additive, actual-average additive, Claim-3.4, and Claim-3.4
  additive variants for that solver-provided feasible pair.
  A two-scale larger-cap package is also available
  for smaller-cap source-min/max comparison IPs, and selected-pair source-min/max
  or additive estimates can feed the one-scale and two-scale search bridges
  directly. The
  two-scale windowed type-assignment provider facade isolates the remaining
  `L LR` source-min/max feasibility obligation without deriving it from the
  weaker `L` window, and now has a source-auto-cap specialization at the
  paper's canonical cap. Load-realizing windowed type assignments now also
  derive the value-pair membership premise internally, giving a standalone
  two-scale source-min/max comparison IP at the proof cap, any larger search
  cap, and the paper's source auto-cap. The source-output wrappers consume the
  direct load/count witness, search-only endpoints expose the resulting
  two-scale search certificate, and provider-shaped variants package
  existential solver output. Generated-rounding Claim-3.4 provider wrappers
  now choose the combined high/low rounding map internally for the one-scale
  source-auto-cap provider route and the two-scale `L LR` windowed
  source-auto-cap provider route. Larger-cap and canonical-cap variants cover
  separate search caps and the paper source-auto-cap proof cap. The
  source-min/max provider route also has source-average larger-cap and
  canonical wrappers deriving `L ≤ LR` and `0 < LR` internally, plus a
  canonical source-average full-IP-summary companion and the analogous
  source-average larger-cap full-IP-summary companion exposing the generated
  comparison IP and bounded full-IP summaries. Exact typed allocation provider
  variants are available as well, including a source-average canonical wrapper
  that derives `L ≤ LR`, `0 < LR`, and the `2 * LR` cap internally, plus a
  larger-search-cap companion with the proof cap fixed to the canonical source
  auto-cap. The exact typed provider route now also has full-IP-summary and
  selected-pair/full-IP companions for the non-windowed source-auto-cap route,
  the source-average canonical two-scale source-auto-cap route, and the
  source-average larger-cap route; the larger-cap full-summary endpoint exposes
  the required `largeCap ≤ 2 * lambda + 4` summary-packaging assumption. Exact
  typed high/low allocations with matching source loads now expose the same
  capped `L LR` type-assignment witness and source-min/max comparison IP
  directly. A standalone selected-pair bridge now
  packages the larger-cap search comparison against the bounded source
  optimum's own min/max pair, with a Claim-3.4 companion. The corresponding
  larger-cap source-min/max source-output packages now also preserve this
  selected-pair forward-ratio payload, including the one-scale, two-scale
  Claim-3.4, windowed exact typed allocation, source-min/max windowed provider,
  load/count, and load/count-provider routes. The remaining work is no longer
  another scalar/additive wrapper layer; it is proving or importing the concrete
  IP/Lenstra runtime theorem and completing the PTAS/FPTAS complexity package.
  The finite-search size
  layer now also
  exposes the rounded
  value-index bound `Fintype.card (RoundedValueIndex lambda) <= lambda^2 + 1`
  and explicit source/two-scale/source-auto-cap type and value-pair search
  bounds using that exponent. The source-auto-cap solver certificate premise is
  named
  `paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation`; it isolates
  the capped concrete-IP witness obligation without asserting Lenstra runtime.
  The external-complexity seam now also has source-average Claim-3.4
  specializations that supply this named obligation internally before applying
  an externally supplied feasible-solver consequence.
  The generated rounded-average cap arithmetic is factored into public helpers
  for `LR ≤ L + extraAverage` and the corresponding source-auto-cap count
  bound.
  The workload, ratio, full-IP-constraint, full-IP-summary, concrete-IP/search,
  and compact ratio solver surfaces now also have `..._of_solver_obligation`
  wrappers that consume this named premise directly, and the source-output
  solver facades expose the same named-obligation route for both scalar-forward
  and additive-forward continuations. The scalar/additive named-obligation
  facades, their Claim-3.4-discharge variants, and the corresponding
  Claim-3.4-certificate facades also have paired full-IP-summary/source-output
  companions. Provider constructors now derive the named obligation from exact
  bounded materialized-supply or typed high/low allocation
  providers, including source-average variants. The source-average Claim-3.4
  route now also discharges this named certificate obligation directly via
  `paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_source_average_claim34_no_top_of_margin`.
  The workload, full-IP, concrete-IP/search, compact ratio, and source-output
  solver surfaces now include direct source-average Claim-3.4 discharge
  wrappers, so callers with the source-average high/low hypotheses no longer
  need to supply the named solver obligation separately.
  The conditional runtime seam now
  uses `EconCSLib.Complexity.ExternalSolverConsequence`, with wrappers returning
  the external consequence alone or paired with the named solver obligation.
  Source-output provider facades now route source-average exact bounded
  materialized-supply and typed high/low allocation providers directly through
  that named obligation, for both scalar-forward and additive-forward
  continuations, including Claim-3.4 bounded-optimum variants. The
  external-complexity seam now has matching source-average exact-provider
  wrappers in both consequence-only and obligation-plus-consequence forms.
  External source-output wrappers now also pair those exact-provider scalar
  and additive continuations with the externally supplied complexity
  consequence. The compact conditional package
  `theorem33ExternalSolverSelectedPairFullSummarySourceOutputPackage` now names
  the strongest selected-pair/full-IP source-output payload together with the
  external solver consequence, and the scalar/additive Claim-3.4 source-average
  endpoints return that package directly.
  A separate owner-map
  materialized-supply bridge,
  `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_owner_no_top_of_weighted_supply`,
  removes the explicit starting-optimum premise when an owner map for the
  materialized rounded items is available.

## Review Plan

- Review the Theorem 2.1/Lemma 2.2/Theorem 2.3/Section 4 support rows against
  the cached source.
- Confirm that the finite-agent/finite-item caveat is visible in the Lean
  statement and reviewer notes.
- Theorem 4.1 is closed by the finite source counterexample; review the
  eight-egg proof simplification against the source proof's 100-egg narrative.
- Theorem 4.2 is closed as an explicit finite probability inequality; review
  the finite bound against the source proof's Chebyshev/union-bound paragraph.
- For Section 3, review the Theorem 3.1 endpoints as source-shaped
  asymptotic lower bounds relative to a middle-pair hard-family sequence; the
  explicit binomial/exponential growth comparison is not separately proved.
- For Claim 3.4, review the branching-potential endpoint as discharging the
  termination/finite-descent assembly from explicit min/max source-model data,
  including the strict high-source, low-only, and strict upper-boundary branch
  constructors, and review the empty-bundle obstruction lemma as justification
  for the remaining positive-minimum premise.

## Next Work

- Adopt the fixed-dimension IP runtime boundary as the main explicit
  assumption for Theorem 3.3. The paper-local plan is to finish and review all
  LMMS04-specific finite allocation, rounding, Claim 3.4, finite search,
  concrete IP-certificate, source-output, and ratio-transfer layers, while
  leaving the Lenstra/fixed-dimension IP runtime theorem as
  `EconCSLib.Complexity.ExternalSolverConsequence`.
- Track the runtime theorem as reusable library work, not paper-local proof
  debt. Prefer a future adapter under
  `EconCSLib.Algorithms.Complexity.FixedDimensionIP` that can consume CSLib
  machine-model/cost semantics, optlib integer-program
  feasibility/optimization semantics, or both, and instantiate the current
  external solver consequence without changing LMMS04 theorem statements.
- Close the remaining Section 3 runtime gap:
  - Claim 3.4: the all-goods finite source wrapper
    `paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods`
    now instantiates the source-domain selector from paper-level data: total
    goods load `#agents * L`, positivity, and strict smallness of every finite
    source good. The selector chooses the nonempty exact starting optimum
    internally via finite search, while
    `paper_lmms_exists_surjective_owner_of_total_strictly_small_positive_values`
    derives an owner map automatically from exact total value and strict
    smallness when the materialized domain is all goods. The older
    unrestricted-optimality wrapper
    `paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods`
    is retained as a compatibility route.
    The empty-bundle obstruction lemma
    `paper_lmms_claim_3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle`
    shows why exact allocation and nonnegative goods are insufficient by
    themselves.
    The branch-step proof itself is now closed for the exact nonempty
    positive-goods source domain by
    `paper_lmms_claim_3_4_branch_step_of_exact_nonempty_positive_goods`.
  - Theorem 3.3: instantiate the abstract external solver consequence with a
    concrete finite-IP/Lenstra runtime theorem; the finite type-space bound,
    per-agent rounded-type assignment and exact/bounded-exact rounded-good
    allocation concrete-IP constructors, Claim 3.4 rounded-types value-pair IP
    constructor, rounded goods-supply weighted accounting, rounded-bundle load
    equality, high-good source-value-to-index rounding,
    rounded-model-from-index bridge, and value-pair search layers are now in
    place, and low-good aggregation into artificial rounded goods is now
    isolated. The combined high-source/low-artificial rounded goods-supply
    vector is also in place, with a direct concrete-IP constructor once the
    solver supplies per-agent rounded bundle types whose coordinate totals
    match that supply. Materialized-supply value accounting, `L`-bounded item
    values, strict `< L` support away from the top rounded index, bounded
    materialized-supply concrete-IP packaging, and the Claim 3.4
    bounded-allocation-to-search bridge plus finite-search existence wrappers
    are also in place, including the no-top hstep-free materialized bridge and
    the combined-high/low type-assignment-to-search wrapper. The no-top
    support of the combined supply is now closed under the explicit high-good
    rounding margin. The two-scale rounded-average search-certificate layer is
    now in place through full-summary capped and auto-cap endpoints, including
    actual-rounded-average wrappers that no longer require an external
    `haverage` premise for the generated auto-cap package. The capped exact
    supply constructor
    `paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_supply_allocation`
    exposes a supplied bounded materialized rounded-supply allocation as a
    capped concrete IP certificate; the typed companion
    `paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_typed_combined_high_low_allocation`
    keeps the provenance-carrying high/low item type through the same capped
    boundary. Also,
    `paper_lmms_theorem_3_3_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`
    packages a bounded-allocation provider into the quantified solver premise.
    The source-auto-cap specialization
    `paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider`
    uses the canonical cap count from the source auto-cap endpoints, and
    `paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_typed_combined_high_low_allocation_provider`
    rewrites exact typed combined allocation providers into that generated
    anonymous-supply premise, and the source-average typed variant
    `paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider`
    derives the rounded-average cap internally from the high/low source-average
    hypotheses, and
    `paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin`
    feeds the typed provider route into the source-auto-cap finite workload
    summary, and its ratio-guarantee companion
    `paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin`
    prefixes the final rounded-instance guarantee. The same typed-provider
    source-average route now also reaches the solver full-IP constraint
    summary, full-IP-constraint ratio endpoint, full-IP summary with ratio
    guarantee, and concrete IP/search full-summary ratio endpoint. The capped
    concrete-IP realization construction now turns the IP counts themselves
    into exact bounded anonymous rounded-supply and typed high/low allocation
    witnesses.
    The stronger source-average specialization
    `paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_supply_allocation_provider`
    removes the explicit rounded-average cap premise by using
    `paper_lmms_theorem_3_3_combined_high_low_rounded_goods_supply_weighted_value_bounds`.
    The workload wrapper
    `paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
    exposes the finite solver-workload summary from that provider route, and
    `paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin`
    adds the rounded-instance ratio guarantee.
    The source-output assembly and ratio-transfer bridge are now in place: the
    exact-low-partition and owner-estimate wrappers build the combined output
    allocation, derive output positivity from the rounded window and
    backward-minimum transfer, and apply the epsilon source-output ratio endpoint
    once the rounded-load identity and either pointwise forward estimates or the
    scalar forward ratio comparison are supplied. The capped-search
    source-output route now pushes the scalar comparison down to selected-pair
    and feasible comparison-IP boundaries, with wrappers for additive pair
    estimates and the source optimum min/max comparison pair. The
    allocation-window
    wrapper now removes the need to state min/max windows separately once
    per-agent rounded and optimal windows are available. The weighted-prefix
    low-good route is now closed through owner filters: maximal prefix floors,
    monotone cumulative cuts, concrete prefix-slice lists, per-slice one-unit
    estimates, the `Fin N` and arbitrary finite-agent specializations,
    slice-to-owner filter construction, owner-load estimates, exact low
    partitions, and finite-prefix source-output ratio endpoints are verified.
    Remaining Theorem 3.3 work is to instantiate the current
    `ExternalSolverConsequence` surface with a concrete IP/Lenstra runtime
    theorem and then package the final PTAS/FPTAS complexity certificate.
