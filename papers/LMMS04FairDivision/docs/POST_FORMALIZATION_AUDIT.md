# Post-Formalization Audit: LMMS Fair Division (2004)

This file preserves the detailed implementation/status ledger that was
previously mixed into `FINAL_VALIDATION_REPORT.md`. The final validation report
is now kept short and human-facing; use this audit file for pickup detail,
verified-surface inventories, exact boundary notes, command history, and next
proof targets.

Status note, 2026-05-26: the deliberate completion plan is to formalize the
LMMS04-specific finite allocation, rounding, IP-certificate, source-output, and
ratio-transfer layers, while treating fixed-dimension integer-program runtime
as a named external complexity boundary. The human-facing status for Theorem
3.3 must remain conditional until `ExternalSolverConsequence` is discharged by
a concrete Lenstra/fixed-dimension IP runtime theorem or equivalent
machine-model result.

Status note, 2026-05-25: this report predates the current full-summary
capped-search verification pass and is retained as historical validation output.
For the current verified state, use `HANDOFF_2026-05-25.md` and
`START_HERE_NEXT_AGENT.md`. Since this report was first written, the Theorem
3.3 surface gained comparison-allocation packages that internally produce the
capped search certificate and source-auto-cap packages for the source-min/max
load/count data route, its provider form, and the exact typed
allocation/load-match route, including canonical-cap comparison-IP
constructors and two-scale exact-typed source-output packages. Some Theorem
3.3 surface details below are historical relative to the current Lean files.
The latest pass also adds solver-to-source-output wrappers for the
source-average route, generic additive-forward route, actual-rounded-average
additive-forward route, Claim 3.4 route, and Claim 3.4 additive-forward route;
the scalar and additive Claim-3.4-discharge routes now also have selected-pair
forward-ratio and full-IP-summary packages.
It also names the exact source-auto-cap solver certificate obligation and adds
explicit `lambda^2 + 1` exponent cardinality bounds for the finite search
surfaces. The principal solver endpoints now have named-obligation wrappers, so
the public interface can consume that single certificate premise directly,
including at the source-output scalar-forward and additive-forward facades.
Exact bounded materialized-supply and typed high/low allocation providers also
construct the named obligation directly. A conditional
`ExternalSolverConsequence` wrapper now records how an external feasible solver
theorem would imply a chosen complexity consequence; the Lenstra/runtime and
PTAS/FPTAS complexity claims remain outside this report's verified Lean
surface.
The source-output layer additionally has direct provider facades from
source-average exact bounded materialized-supply and typed high/low allocation
providers, in scalar-forward, additive-forward, and Claim-3.4 variants.
The latest source-auto-cap pass also proves the named solver certificate
obligation directly from the source-average Claim 3.4 rounded-supply bridge
and wires that discharge through the lower solver summaries and source-output
facades. The source-output packages now expose the selected-pair/full-IP
payloads needed to keep the solver witness and source allocation witness tied
together.
The current generated-rounding pass also packages the source-min/max provider
route directly: one-scale and two-scale Claim-3.4 wrappers choose the combined
high/low rounding map internally and then consume the source optimum's own
load/count provider witness, including larger-cap and canonical-cap two-scale
variants and parallel exact typed combined-allocation provider wrappers. The
source-average source-min/max larger-cap and canonical wrappers derive `L ≤ LR`
and `0 < LR` internally. The canonical source-average source-min/max route also
has full-IP-summary companions at both the canonical source auto-cap and an
explicit larger search cap, exposing the generated comparison IP and standard
bounded full-IP summaries. The larger-cap companion assumes
`largeCap ≤ 2 * lambda + 4`. The source-average exact-typed
canonical wrapper derives those rounded lower-bound facts plus the `2 * LR` cap
condition internally. The exact-typed route also has a larger-search-cap
source-average wrapper with the proof cap fixed to the canonical source
auto-cap. The exact-typed generated/provider route now also exposes
full-IP-summary companions for the non-windowed source-auto-cap endpoint, the
source-average canonical two-scale source-auto-cap endpoint, and the
source-average larger-cap endpoint; the larger-cap full-summary wrapper carries
the `largeCap ≤ 2 * lambda + 4` bounded-summary premise.
The external-complexity seam now has source-average Claim-3.4 wrappers that
feed the verified named certificate obligation into an externally supplied
feasible-solver consequence, plus matching source-average exact bounded
materialized-supply and typed high/low allocation provider wrappers.
The external source-output layer also has paired exact-provider scalar-forward
and additive-forward wrappers returning the verified source-output package
together with that externally supplied consequence, and record-style scalar and
additive selected-pair/full-IP source-output wrappers returning
`ExternalSolverConsequence.Consequence`.
The source-auto-cap arithmetic also now exposes reusable generated-average and
generated-cap-count helpers for the exact weighted average `LR`.

## Current Verdict

The paper is partially formalized. The Section 2 bounded-envy existence path is
closed for the real-supported interval model of the paper's `[0,1]` measurable
space, and Section 4 is formalized through finite source-facing truthfulness
and randomized concentration endpoints. Section 3 now has substantial support,
including the Theorem 3.1 adaptive asymptotic query wrapper. Claim 3.4 now has
both high-source and low-only descent potentials plus a finite lexicographic
branch assembly endpoint, including the strict upper-boundary branch, and the
paper-facing row now exposes an exact finite-allocation wrapper that derives
the average-load, ownership, item-domain, and move-update plumbing from
`IsAllocationOf`. The high-good source-value-to-index rounding seam and the
low-good artificial-supply aggregation seam are now closed, as is the combined
high-source/low-artificial rounded goods-supply vector and the direct
concrete-IP seam for type assignments over any specified rounded supply.
Materialized rounded-supply item values are now positive and bounded above by
`L`, with a strict `< L` criterion for non-top rounded indices; combined-supply
materialized value bounds, standalone concrete-IP packaging for bounded
materialized-supply allocations, and the Claim-3.4-to-search bridge over
materialized supply are also closed. The finite value-pair search can now be
constructed by classical finite minimization from any feasible value-pair IP,
with paper-facing wrappers for concrete IP certificates, supply assignments,
bounded materialized-supply allocations, and Claim 3.4 min/max IP certificates.
The exact nonempty positive-goods Claim 3.4 branch step is now discharged
internally, and the no-top materialized rounded-supply bridge no longer takes a
raw branch-step premise. It still requires the source-shaped total-load and
strict-smallness/no-top premises.
The concrete runtime/Lenstra solver layer and final PTAS/FPTAS complexity claim
remain open; the current Lean surface packages the verified solver/source-output
payloads up to an abstract `ExternalSolverConsequence`.

## Major Assumption: Fixed-Dimension IP Runtime

The main formalization assumption is intentional and explicit: Theorem 3.3's
final PTAS/FPTAS runtime conclusion is conditional on an external
fixed-dimension integer-program solver theorem. In Lean this is represented by
`EconCSLib.Complexity.ExternalSolverConsequence`.

This means the planned verification boundary is:

- Formalize all LMMS04-specific finite mathematics, rounding constructions,
  Claim 3.4 consequences, finite search spaces, concrete IP certificates,
  source-output payloads, and ratio-transfer wrappers.
- Assume, until separately proved or imported, the general algorithmic theorem
  that the fixed-dimension IP instances generated by the formalized search can
  be solved within the runtime needed for the paper's PTAS/FPTAS conclusion.
- Keep the final paper-facing PTAS/FPTAS theorem conditional or absent until
  that external theorem has a real Lean proof.

This is not another hidden fair-division lemma. It is the reusable complexity
theorem corresponding to the paper's invocation of fixed-dimension integer
programming. The preferred forward path is a small adapter theorem, probably
under `EconCSLib.Algorithms.Complexity.FixedDimensionIP`, that instantiates
`ExternalSolverConsequence` from upstream library work. CSLib is the natural
candidate for machine-model/cost semantics; optlib is the natural candidate for
integer-program feasibility/optimization specifications. LMMS04 should keep its
current `ExternalSolverConsequence` boundary so either library, or a combined
adapter using both, can discharge the assumption without rewriting the paper
interface.

The finite indivisible-goods core is in good shape: the paper definitions,
Lemma 2.2, Theorem 2.1 existence, and the constructive algorithm correctness
surface compile. The current pass closed the measure partition route for
Theorem 2.3: aggregate point masses above `alpha / 2` are split into singleton
pieces, the residual aggregate measure is partitioned into finitely many
low-mass interval pieces, and Theorem 2.1 allocates the resulting finite goods.
Theorem 4.1 and Theorem 4.2 also compile with their source-facing finite
counterexample and randomized concentration statements.

The remaining open work is Section 3's runtime/complexity instantiation. The
current interface now closes the
capped-IP realization step: a capped concrete IP can be materialized as an
exact bounded rounded-supply allocation, including the provenance-carrying
typed combined high/low variant, via
`paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap`
and
`paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap`.
The analogous `..._of_search_certificate_with_cap` endpoints apply the same
realization to the chosen IP stored in capped value-pair search certificates.

## Verified Surface

Human reviewers should start from `PaperInterface.lean`.

Closed or source-interface endpoints:

- Paper definitions: allocation, envy, envy-free, bounded envy, maximum
  marginal item value.
- Lemma 2.2: finite envy-cycle elimination gives an acyclic envy graph while
  preserving the allocated goods and envy bound.
- Theorem 2.1: finite bounded-envy allocation existence.
- Theorem 2.1 constructive form: the LMMS algorithm returns an allocation of
  the input list's `toFinset` with envy bounded by `alpha`.
- Lemma 2.4 / Theorem 2.3: for real measures supported on an interval, bounded
  paper atoms imply a finite high-point split plus residual low-mass partition;
  Theorem 2.1 allocates those finite pieces with envy at most `alpha`.
- Theorem 4.1: the finite two-player/eight-egg source counterexample proves
  that any direct mechanism that always allocates the source goods and returns
  an envy-free allocation whenever one exists is not truthful. The minimum-envy
  form follows from the minimum-envy-to-envy-free bridge.
- Theorem 4.2 support: the independent uniform random allocation mechanism is
  formalized, and report-independent randomized allocation laws are truthful in
  expected utility.
- Theorem 4.2 concentration: normalized additive values with every item worth
  at most `alpha` imply the explicit finite probability bound
  `Pr[max envy <= t] >= 1 - 2 * alpha * n / t^2` for the uniform random
  assignment law.
- Theorem 3.1 support: the finite hard-family construction, middle-layer
  complement-pair counting, swapped-profile obstruction, two-bit query-count
  cardinal bridge, adaptive deterministic value-query endpoints, and
  eventual/asymptotic lower-bound wrappers for both minimum envy and minimum
  envy-ratio compile.
- Theorem 3.2 support: Graham's `1.4 = 7 / 5` cited approximation theorem is
  represented as a certificate-to-envy-ratio wrapper.
- Claim 3.4 support: the high-source move into a bundle of load at most `L` is
  ratio-nonincreasing, strictly decreases the global
  `overfullBundleCardPotential`, and feeds a finite-descent assembly theorem.
  The low-only positive max-to-min small-item lemma, ratio-nonincreasing local
  move certificate, no-high primary-potential preservation, and
  `minLoadTiePotential` descent theorem are also formalized, and
  `claim34_certificate_of_branching_potential_descent` combines the high-source
  and low-only branches by finite lexicographic descent.
  `claim34_boundary_branch_step_of_min_max_source_move` closes the strict
  upper-boundary branch, and
  `claim34_branch_step_of_minmax_source_trichotomy` proves the full source
  min/max case split from the local invariants. The exact-allocation wrapper
  `paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations` uses
  `IsAllocationOf` to supply ownership, goods-domain item bounds, average-load
  preservation from total goods load, exact `moveBundle` preservation, and the
  concrete `moveBundle` update law.
  The positive-minimum premise is reduced by positive-bundle and
  nonempty-positive-good wrappers, including
  `paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods`.
  The exact nonempty positive-goods branch step
  `paper_lmms_claim_3_4_branch_step_of_exact_nonempty_positive_goods` keeps the
  concrete `moveBundle` witness visible in all three min/max cases, uses
  `paper_lmms_isAllocationOf_moveBundle` for exactness, and proves nonempty
  preservation from the donor-load gap. The hstep-free wrapper
  `paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods`
  packages this branch step with the finite-descent theorem.
  The obstruction lemma
  `paper_lmms_claim_3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle`
  also proves that an exact allocation with an empty bundle and nonnegative
  goods has zero minimum common load, so the positive-minimum premise cannot be
  derived from exact allocation alone.
- Theorem 3.3 / Lemma 3.5 support: the identical-utilities load model,
  rounded-type/IP certificate seam, finite bounded-type enumeration for the
  source search set `U`, finite value set `V(U)`, source interval slice
  `U_{u1,u2}`, concrete goods-supply IP equations, finite value-pair search
  certificate and size bound, rounded goods-supply weighted-value accounting,
  concrete IP construction from an explicit per-agent rounded-type assignment,
  from exact rounded-good allocations, and from bounded exact rounded-good
  allocations using their own rounded min/max load pair, rounded-bundle load
  equality, concrete-IP search optimality wrapper, exact-allocation and
  exact-bounded-allocation search optimality, high-good source-value-to-index
  rounding, low-good aggregation into artificial goods of value `L / lambda`
  with a one-unit overshoot bound, the rounded model induced by a source-good
  index map, Claim 3.4
  min/max-to-rounded-value-pair bridge, Claim 3.4 rounded-types value-pair IP
  constructor, search optimality against a Claim 3.4 min/max IP certificate,
  finite-search existence from Claim 3.4 min/max IP certificates, concrete IP
  construction plus search optimality and search existence over externally
  specified rounded supply vectors, materialized rounded-supply value accounting,
  `L`-bounded item values, strict `< L` support away from the top rounded
  index, top-index strictness criteria, bounded materialized-supply concrete-IP
  packaging and search existence, combined-supply materialized value bounds,
  Claim-3.4-to-search comparison on
  materialized supply, bundled final ratio/concrete-IP summary, and additive
  ratio-transfer algebra through the paper's `lambda = 56 / epsilon` endpoint
  compile. The capped search layer now also has a direct capped concrete-IP
  constructor from bounded exact materialized-supply allocations, a generic
  bounded-allocation-provider-to-solver-premise bridge, source-auto-cap
  specializations of that bridge, and a reusable high/low combined-supply
  weighted-value bound. The source-average exact-allocation-provider workload
  wrapper routes those ingredients into the source-auto-cap finite solver
  summary and the rounded-instance ratio endpoint. The same source-average
  provider route now also exposes solver full-IP constraint, full-IP constraint
  ratio, full-IP summary ratio, and concrete IP/search full-summary ratio
  endpoints. The actual-rounded-average route also pairs its full-IP summary
  with the generic source-average and Claim-3.4 source-output packages for
  scalar-forward and additive-forward continuations, and the scalar/additive
  named-obligation solver facades, their Claim-3.4-discharge variants, and the
  corresponding Claim-3.4-certificate variants have the same paired
  full-IP/source-output companions. The transfer layer now also
  has a per-agent allocation-window wrapper that derives the rounded/optimal
  min/max load windows used by the Lemma 3.5 algebra, plus a backward-min
  variant deriving the output positive-minimum premise from the rounded window
  and backward minimum transfer estimate. The current transfer support also
  includes a Claim-3.4-certificate wrapper, a load-function agentwise transfer
  endpoint for different item types, a concrete source-output/rounded
  allocation ratio-transfer wrapper, a high-good bundle-load scaling helper, a
  high/low forward-transfer helper from a supplied low artificial-load
  estimate, high/low backward-transfer helpers from supplied low-load
  estimates, agentwise forward/backward transfer wrappers, a low-good
  owner-map partition boundary, combined low-partition endpoints for forward,
  backward, two-way, and `lambda = 56 / epsilon` transfer forms, a
  four-premise owner-estimate wrapper matching the additive load-transfer API,
  a matching exact-low-partition four-premise wrapper, an
  exact-allocation-to-owner helper, an exact-low-partition-to-owner-load
  bridge, a low-owner/low-partition equivalence theorem, an owner-filter
  exact-allocation helper, and the ordered weighted-prefix skeleton for the
  low-good construction: maximal prefix floors, monotone cumulative cuts,
  concrete prefix-slice lists, per-slice one-unit load estimates, and a `Fin N`
  plus arbitrary finite-agent target specialization, with an adapter and
  slice-to-owner construction that turn represented slice sums into
  owner-filter estimates, exact low partitions, and finite-prefix source-output
  ratio endpoints. The high/low source-output assembly layer also
  unions exact high and low allocations over disjoint goods, proves the
  common-load decomposition, returns the combined source output allocation with
  the four additive transfer premises, derives output positivity from the
  rounded window and backward-minimum transfer, and applies the final epsilon
  source-output ratio transfer for the exact-low-partition and owner-estimate
  routes once the rounded-load identity and forward optimal-to-rounded estimates
  are supplied; the new scalar-forward variants instead consume the
  solver-shaped ratio premise
  `roundedRatio <= sourceOptimalRatio * forwardTransferFactor`. The capped
  search source-output bridge now also consumes selected-pair or feasible
comparison-IP premises, including additive-pair and source-min/max
comparison-IP variants. A standalone selected-pair bridge now bounds the
larger-cap source-min/max search result against the source optimum's min/max
ratio, with a Claim-3.4 companion. The larger-cap source-min/max source-output
packages now also preserve that selected-pair forward-ratio witness, including
the one-scale source-min/max package, the Claim-3.4 packages, and the two-scale
windowed exact typed allocation route, plus source-min/max windowed provider
and load/count routes; an exact bounded typed comparison allocation can also
build the capped comparison IP internally before consuming either a scalar
forward-ratio premise or additive pair estimates. The source-min/max
comparison route now has a direct type-assignment constructor for the capped
  comparison IP, load/count variants, and larger-cap finite-search wrappers
  from smaller-cap feasible IPs. Exact
  materialized low artificial allocations now provide the
  aggregated low total internally, and exact allocations of the typed combined
  high/low materialization project to high source allocations, extracted low
  loads, rounded-load decomposition, source-output ratio transfer, and a
  concrete IP certificate for the explicit high-plus-low supply vector. The
  typed combined layer now also exposes final ratio/search endpoints, capped
  concrete-IP constructors, a source-auto-cap solver-premise bridge from typed
  allocation providers, the source-average typed-provider specialization, a
  typed-provider finite workload wrapper and ratio endpoint, and a
  source-output-plus-search endpoint for the same exact typed allocation.
  The new finite-search existence endpoints are
  `exists_roundedValuePairSearchCertificate_of_feasible_pair`,
  `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_concrete_ip`,
  `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_supply_type_assignment`,
  `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_supply_allocation`,
  and `paper_lmms_theorem_3_3_exists_value_pair_search_certificate_claim_3_4_min_max`.

## Important Boundaries

Theorem 2.3 is formalized in the real-supported interval representation:
support is stated as zero aggregate mass outside the chosen real interval. This
matches the paper's `[0,1]` Borel setting by taking an interval containing
`[0,1]`; the Lean statement is slightly more general because it only needs
finite measures and the support/atom hypotheses used by the proof.

Theorem 4.1 is closed for the finite source counterexample. The source paper
uses 100 eggs; Lean uses an eight-egg instance with the same two-case
manipulation argument. Since Theorem 4.1 is an impossibility result, this
smaller finite instance is enough for the counterexample.

Theorem 4.2 is formalized as the finite bound used in the source proof. The
paper's asymptotic Big-O wording is represented by this explicit finite
Chebyshev/union-bound inequality rather than by a separate asymptotic
notation wrapper.

Theorem 3.1 is formalized as a source-shaped asymptotic wrapper relative to a
sequence of middle-complement-pair certificates: if `2*q/#middle-pairs -> 0`,
then deterministic adaptive two-bit value-query algorithms eventually fail for
both minimum envy and minimum envy-ratio. The explicit binomial estimate turning
the concrete middle layer into a standalone "exponential in the number of
goods" growth statement is not separately formalized.

Claim 3.4 is formalized with the same finite/exact-allocation caveats recorded
in the public paper table. Lean now proves finite descent from the
paper's high-source local reallocation move using a global
overfull-bundle-card potential; it also proves the complementary low-only
finite tie-breaker route, a domain-restricted lexicographic finite-descent
theorem over an explicit feasible set, an exact positive-minimum allocation
wrapper, a concrete branching-potential specialization, an exact
nonempty-allocation wrapper under positive goods, and the same concrete
branching-potential specialization in that nonempty-positive domain. A
read-only proof-route audit found that the low-only
case cannot be closed from the overfull-bundle potential: when no bundle is
above `2L`, that potential is already zero. Lean now supplies the branch pieces:
`exists_pos_item_lt_max_sub_min_of_low_min_average` gives a positive small
max-bundle item, `exists_low_min_max_source_move_ratio_nonincreasing` packages
the max-to-min move as a ratio-nonincreasing local reallocation certificate,
`overfullBundleCardPotential_eq_of_low_only_move_no_high` preserves the zero
primary potential, and `minLoadTiePotential_decreases_of_low_only_move` proves
descent for the finite min-load rank/multiplicity potential. The theorem
`claim34_low_only_branch_step_of_move_certificate` packages those facts with a
ratio-nonincreasing move certificate, and
`claim34_low_only_branch_step_of_min_max_source_move` derives that low-only
branch directly from min/max accessor data. The matching
`claim34_high_source_branch_step_of_min_max_source_move` derives the strict
high-source branch, and
`claim34_boundary_branch_step_of_min_max_source_move` derives the strict
upper-boundary branch where all loads are above `L / 2` and the maximum load is
exactly `2 * L`. The theorem
`claim34_branch_step_of_minmax_source_trichotomy` combines all three local
branches, and `claim34_certificate_of_minmax_source_trichotomy` wires that
source step into finite lexicographic descent. The concrete wrapper
`claim34_certificate_of_concrete_minmax_source_trichotomy` instantiates the
min/max accessors with canonical finite minimum and maximum bundle loads, and
`paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations` specializes the
source-data assembly to exact `Allocation` objects. The wrapper
`paper_lmms_claim_3_4_bounded_optimal_on_exact_nonempty_positive_goods`
reduces the domain-restricted route to exact nonempty allocations when all
source goods are positive. The wrapper
`paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods_branching_potentials`
then lifts the nonempty-positive optimality conclusion back to all exact
allocations. The hstep-free wrapper
`paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods`
now discharges the exact nonempty positive-goods branch step from the min/max
trichotomy. The all-goods wrapper
`paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods`
now also discharges the source-domain selection step from exact total load,
positive values, and strict smallness in the finite source-good domain.
The exact `moveBundle` source-domain preservation lemma is isolated as
`paper_lmms_isAllocationOf_moveBundle`, and nonempty preservation is captured by
`paper_lmms_moveBundle_nonempty_of_source_load_gt_item` and
`paper_lmms_moveBundle_nonempty_of_gap`. Lean also records the boundary
obstruction:
`paper_lmms_claim_3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle`
shows that if an exact allocation has an empty bundle and all goods have
nonnegative value, its minimum common load is zero.

Theorem 3.3 is still certificate-level for the algorithmic construction. Lean
proves the rounded-type/IP certificate seam, the bounded finite type-space
enumeration and cardinal bound used by the source proof, the finite value set
`V(U)`, ordered value-pair search bound, interval slice `U_{u1,u2}`, concrete
goods-supply IP equations, rounded goods-supply weighted-value accounting,
finite search certificate and size-bound wrapper, concrete IP construction from
explicit assigned rounded bundle types, exact rounded-good allocations, and
bounded exact rounded-good allocations, high-good source-value-to-index
rounding, low-good artificial-supply aggregation with the source one-unit
overshoot bound, rounded-bundle load equality, concrete-IP search optimality
wrapper, finite-search existence from feasible value-pair IP certificates,
exact-allocation and exact-bounded-allocation search optimality, the rounded
model induced by a source-good index map, and Claim 3.4 min/max-to-rounded
value-pair, value-pair IP, search-optimality, and search-existence bridges,
plus a bundled final ratio/concrete-IP summary and Lemma 3.5 additive transfer
algebra, and the combined high-source/low-artificial rounded goods-supply
vector. Lean also materializes arbitrary rounded supply vectors as finite
rounded items and gives a direct concrete-IP constructor for a per-agent
rounded-type assignment whose coordinate counts equal any specified supply.
The materialized supply has positive and `L`-bounded item values, strict `< L`
support when the rounded index is below `lambda^2`, exact weighted-value
accounting, top-index strictness criteria, and standalone concrete-IP and
finite-search-existence constructors for bounded exact allocations of that
materialized supply; the combined high/low supply now inherits the source error
bounds after materialization. The source-auto-cap solver-premise bridge now
specializes the bounded exact materialized-allocation provider route to the
canonical cap count, with a source-average variant that derives the needed
rounded-average cap internally and a workload wrapper that exposes the finite
solver summary and ratio endpoint from exact bounded allocation providers. The
agentwise transfer layer also accepts per-agent rounded/optimal load windows
directly before assembling the rounded-instance search certificate. The no-top
endpoint
`paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top`
routes an exact optimal materialized allocation through Claim 3.4 without an
external branch-step premise, assuming total value `#agents * L` and zero
top-index supply. The companion
`paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top_of_weighted_supply`
uses the weighted rounded-supply average equation directly. Later passes add
the source-auto-cap solver-obligation, selected-pair/full-IP source-output, and
external-consequence wrapper layers; the concrete IP/Lenstra runtime theorem
and final PTAS/FPTAS complexity claim remain outside the verified Lean surface.

## Validation Checks

Recent checks run:

```bash
lake build LMMS04FairDivision.MainTheorems
lake build LMMS04FairDivision.PaperInterface
lake build LMMS04FairDivision.Theorem31Asymptotic
lake build LMMS04FairDivision.Theorem33RoundedConstruction
lake build LMMS04FairDivision.Theorem34LocalReallocation
lake build LMMS04FairDivision.Theorem35RoundingTransfer
lake build EconCSLib.Foundations.Probability.RealIntervalPartition
lake build LMMS04FairDivision.Theorem41Witnesses
lake build LMMS04FairDivision.Theorem42Concentration
lake build LMMS04FairDivision
rg -n '\b(sorry|admit|axiom|placeholder|TODO|FIXME)\b' papers/LMMS04FairDivision EconCSLib/SocialChoice/FairDivision --glob '*.lean'
git diff --check -- README.md docs/ECONCSLEAN_CURRENT_STATUS.md papers/LMMS04FairDivision EconCSLib/SocialChoice/FairDivision EconCSLib/Foundations/Probability/RealDistribution.lean
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
./review-dashboard.sh --check
python3 scripts/audit_repository.py
```

The dashboard check reports `0/33` reviewed, `33` needing attention, `0`
stale, and `0` mismatched. The nonzero exit is expected until a human reviewer
records those checks.

`python3 scripts/audit_repository.py` still reports one LMMS04
repository-audit finding that is metadata-only: the cached source PDF is
absent. The compact interface now has 33 source-facing review rows selected by
`status.json` `review_surface`; broad proof-facing aliases are in
`ProofInterface.lean`.

Lean footprint at the latest public interface split: 80,220 paper-local Lean
lines across 23 files. `PaperInterface.lean` is 171 lines; the broad
compatibility surface is `ProofInterface.lean`.

## DAG Audit

`DependencyDAG.tex` was rerendered successfully. The DAG keeps the paper's
named-result topology and marks Section 3 nodes as partial where the concrete
Lenstra/runtime instantiation and final PTAS/FPTAS packaging remain open. The
finite Claim 3.4 all-goods source-selection wrapper is now present. No
node-overlap or arrow-through-text issue is known after the latest render.

## Reusable Proof Lessons

- Keep query lower bounds in three layers: hard-family separation,
  transcript-count pigeonhole, and query-model transcript generation.
- For local-reallocation arguments, use a global natural-number potential over
  the whole allocation, not a local donor-only measure, before invoking finite
  descent.
- Keep rounded/PTAS runtime claims as explicit external consequences until the
  concrete Lenstra/machine-model proof is actually formalized.

## Next Proof Targets

1. Finish and review the LMMS04-specific finite proof surface around the compact
   external package.
2. Separately, instantiate the abstract external solver consequence with a
   concrete Lenstra/fixed-dimension IP runtime theorem, preferably through a
   CSLib/optlib-compatible adapter, then package the final PTAS/FPTAS complexity
   statement.
