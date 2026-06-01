# LOS02 Formalization Plan

Last updated: 2026-05-24

## Current State

- `PaperInterface.lean` exposes the formalized combinatorial-auction utility and
  critical-price truthfulness surface.
- `MainTheorems.lean` re-exports the supporting auction-library statements.
- Theorem 4.1 and Proposition 4.2 are represented by the generalized Vickrey
  auction generated from a welfare-maximizing allocation rule with Clarke pivot
  payments. The truthfulness theorem is unrestricted over direct reports; the
  truthful-utility nonnegativity theorem assumes the source type-space condition
  that bundle values are nonnegative.
- Theorem 6.1's reduction layer is represented: maximum clique instances
  reduce to maximum independent set by graph complementation, graph
  independent-set instances are encoded as edge-incidence weighted set-packing
  instances, weighted set-packing selections are encoded as single-minded bids,
  and Lean proves feasibility/value preservation, clique/independent-set/
  set-packing/single-minded threshold-decision preservation, exact optimality,
  solver-transfer, and approximation preservation across those encodings.
  Conditional wrappers
  transfer any external set-packing hardness or inapproximability theorem
  through the compiled LOS02 encoding, including named wrappers for the
  abstract `NP = ZPP` consequence over
  `EconCSLib.Complexity.ComplexityClassModel`. The source complexity-class note
  after Theorem 6.1 is also represented through
  `EconCSLib.Complexity.RandomizedComplexityClassModel`: `P = NP` implies
  `NP = ZPP`, and `NP = ZPP` implies the packaged `NP = RP`, `NP = co-RP`, and
  `NP = co-NP` collapse. The external NP-hardness, polynomial-time,
  randomized-class, and machine-level complexity semantics themselves are not
  modeled in the current library.
- Definition 7.1's average amount per good and Theorem 7.2's square-root-norm
  algebraic approximation endpoint are exposed. The concrete LOS02
  deterministic order by decreasing average amount per good is now represented
  as a finite sort with bidder tie-breaks, and it is proved duplicate-free,
  exhaustive, average-descending, and stable after erasing a bidder whose value
  alone was changed. This stability is also exposed in split form: if the
  original order is `before ++ j :: base`, then the updated order with `j`
  erased is `before ++ base`. Theorem 7.2 is now closed for any sorted explicit
  greedy order containing the optimal bids: the proof exposes the source
  rejected-bid blocker step, packages reduced disjoint instances into
  order-level blocking certificates, proves the blocking-certificate counting
  bound, filters away bids touching goods requested by bids common to the
  optimal and greedy accepted sets, applies the reduced disjoint theorem, and
  uses the common-bid add-back bridge to lift the bound to the original optimal
  and greedy sets. The zero-goods case is handled internally from the
  nonempty-demand and goods-containment hypotheses.
- The greedy allocation fold over an explicit order is represented, and the
  paper's concrete average-order accepted set and allocation are exposed. The
  accepted set is proved pairwise disjoint, and the induced allocation is
  feasible when accepted desired bundles are contained in the goods set.
- Greedy-run blocker extraction is formalized: a denied bid that appears in the
  order has an earlier accepted conflicting blocker, and sortedness gives the
  square-root-norm comparison used in Theorem 7.2.
- Theorem 9.6 now has a source-shaped accepted-set endpoint for single-minded
  bid profiles. Exactness is built into the accepted-set allocation model, and
  monotonicity, participation, and a finite-or-infinite critical-value
  certificate imply truthfulness for nonempty, nonnegative single-minded
  declarations. A domain-aware certificate variant now proves the same
  truthfulness theorem while requiring the critical-value clauses only on the
  source nonempty, nonnegative report domain.
- Lemmas 9.1--9.5 are exposed as named paper-facing support. Lemma 9.1
  constructs the finite-or-infinite acceptance threshold from source-domain
  monotonicity using the infimum of accepted nonnegative values. Lemmas
  9.2--9.5 expose the denied-utility, truthful-utility, value-only deviation,
  and critical-threshold monotonicity consequences used by Theorem 9.6.
- Definition 10.1's payment formula is represented from a supplied `n(j)`
  next-denied function, including the denied/no-next zero-payment cases and the
  `|s_j| * c(n(j))` payment case. The prefix-local `n(j)` search is also
  represented from an explicit split of the sorted greedy order into bids before
  `j`, bid `j`, and the suffix after `j`; the public interface now also exposes
  a full-order `n(j)` search, per-bid payment rule over the sorted greedy
  order, and concrete average-order payment rule. The prefix-local search now
  proves that a returned `n(j)` has no
  earlier denied-because-of candidate in a duplicate-free displayed suffix,
  identifies the exact split state where `n(j)` is denied because of `j`, and
  proves that erasing `j` makes that `n(j)` bid accepted in the corresponding
  erased/lowered run. The fixed-order rejection skeleton is also proved: if the
  erased/lowered order places `j` after its conflicting `n(j)` blocker, then
  `j` is rejected. The Section 10 average-order algebra is exposed: below
  `|s| * c(n)` implies lower average amount per good, and an average-descending
  order cannot place the lower-average bid before the higher-average bid; above
  `|s| * c(n)` gives the symmetric ordering. The value-only update operation
  preserves desired bundles and conflicts, and the changed-order repositioning
  lemmas now combine average-descending sortedness with non-`j` erase-stability:
  below threshold the updated order displays the original `n(j)` before `j`,
  while above threshold it displays `j` before the original `n(j)` position.
  The local finite critical-window theorem composes these facts with the
  erased-blocker and no-candidate-prefix lemmas. A finite accepted-branch theorem
  packages this local window back into the full greedy accepted-set mechanism:
  for an accepted bid with `n(j) = n`, values below `|s_j| * c(n)` are rejected,
  values above it are accepted, and the actual greedy payment equals
  `|s_j| * c(n)`. The accepted no-next branch is also packaged as a zero
  threshold over the nonnegative value domain: nonnegative values below zero are
  impossible, every positive value is accepted from the no-candidate erase-stable
  window, and the actual greedy payment is zero. A full-order source sorted
  window package now derives the finite and no-next local branches from a split
  of the original greedy order around `j`. The concrete sorted order discharges
  the global sortedness/duplicate-free/membership and non-`j` erase-stability
  obligations for value-only changes, including a split-form package around
  `before ++ j :: base`. The ordered-insertion suffix window removes the
  original prefix and proves local acceptance of `j` equivalent to full updated
  average-order greedy acceptance. The public interface also exposes the source
  movement lemma saying a strengthened nonnegative single-minded report moves
  weakly earlier in the concrete average order. Consequently, any accepted
  bidder in the concrete average-order run now has source critical-branch
  windows, and its actual Definition 10.1 payment is proved to be the critical
  threshold for value-only changes on the nonnegative report domain. Definition
  10.1 itself is closed as a concrete paper-facing payment rule; the surrounding
  criticality lemmas remain exposed as support for Theorem 10.2.
- Theorem 10.2 now has a fixed-target critical-price certificate form: if a
  greedy allocation/payment implementation is extensionally a target-bundle
  threshold mechanism with Definition 10.1 prices, and those prices are
  own-report independent, it inherits the existing truthfulness theorem for
  nonempty single-minded profiles. A specialized endpoint now instantiates this
  certificate shape with the full-order Definition 10.1 payment rule.
- Theorem 10.2 also has a source-shaped accepted-set certificate form for the
  actual greedy accepted set and full-order Definition 10.1 payment rule.
  Participation is proved directly from the payment formula. Monotonicity is
  proved from an explicit order-moves-earlier certificate matching the source's
  strengthened-report argument when that certificate is supplied. The
  accepted-set theorem now also has a nonnegative-domain critical-certificate
  endpoint. The concrete average-order source branch data, nonnegative
  critical-value certificate, and nonnegative-domain monotonicity proof are now
  constructed, so the specialized average-order Theorem 10.2 endpoint proves
  truthfulness directly on the source nonempty nonnegative single-minded
  domain.
- Theorem 7.2 and Theorem 10.2 are both represented as paper-facing endpoints.
  Theorem 6.1's reduction surface is represented, including clique complement,
  graph incidence, threshold-decision reductions through set packing and
  single-minded welfare, exact solver transfer, approximation preservation, and
  conditional external complexity-consequence wrappers with reduction-closed
  hardness-transfer and named abstract `NP = ZPP` conclusions. Theorem 7.2's
  source blocker/counting path and Theorem 10.2's strengthened-report
  average-order movement path are exposed. The short source note on complexity
  classes is represented by abstract randomized-class collapse wrappers. The
  only remaining source-level boundary is native computational-complexity
  modeling for NP-hardness, polynomial time, and randomized complexity classes.

## Review Plan

- Review the current interface theorem rows against the source paper.
- Review the Theorem 6.1 rows as a scoped complexity boundary: the clique,
  graph, set-packing, threshold-decision, exact-solver, approximation-solver,
  reduction-closed hardness, and conditional transfer reductions are closed,
  and the abstract `NP = ZPP` plus randomized-class note consequences are
  named, but the repo has no machine-level NP-hardness/ZPP formalism.
- Keep dashboard notes explicit about the limited target-bundle critical-price
  scope.
- Review the Theorem 7.2 endpoint against the source proof: the disjoint case,
  rejected-bid blocker extraction, blocking-certificate counting, common-bid
  filtering, add-back algebra, and zero-goods boundary are now formalized in
  the sorted-order statement.
- Review the Lemma 9.1--9.5 surface as source-domain threshold support:
  Lemma 9.1 proves threshold existence from monotonicity, while payment equality
  to finite thresholds remains the separate Critical axiom consumed by Theorem
  9.6.
- Review the Definition 10.1 payment surface against the source: the paper's
  concrete sorted order rule and concrete payment rule are represented, the
  denied/no-next/next payment cases are exposed, and the order is proved
  average-descending, duplicate-free, exhaustive, and globally erase-stable
  under single-bidder value changes, including the split form for displayed
  `before ++ j :: base` orders. The local suffix-window bridge and accepted-bid
  average-order source-window construction are now compiled; the all-bidder
  nonnegative-domain critical-value certificate and concrete average-order
  nonnegative-domain monotonicity theorem are also compiled, with the
  strengthened-report average-order movement lemma exposed separately.
- Keep the interface rows focused on source-facing named statements; Theorem
  7.2's WLOG common-bid-removal bridge is now represented in Lean.

## Next Work

- Start future pickup from `START_HERE_NEXT_AGENT.md` and the full
  `HANDOFF_2026-05-24.md` note.
- Leave native Theorem 6.1 NP-hardness/NP=ZPP consequences as an explicit
  complexity-library boundary unless the repo later adds machine-level
  computational complexity classes, polynomial-time algorithms, randomized
  algorithms, and concrete reductions. The current conditional wrappers are the
  intended paper-facing bridge to external complexity facts.
- If taking on that library project, define semantic `P`, `NP`, `RP`, `co-RP`,
  `ZPP`, and `co-NP`, instantiate polynomial-time many-one reductions for the
  compiled clique/set-packing/single-minded maps, and then replace the
  external Karp/Hastad-style hardness hypotheses with native theorems.
- Keep Theorem 10.2 review focused on the source-domain interpretation: the
  concrete average-order endpoint is closed for nonempty nonnegative
  single-minded profiles, while global monotonicity over arbitrary negative
  reports is intentionally not claimed.
