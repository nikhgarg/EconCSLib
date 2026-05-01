# Mechanism Design and Auctions

Use for `EconCSLib/MechanismDesign/Auctions/*`, digital goods, GSP/position
auctions, combinatorial auctions, and generic mechanism-design wrappers.

## Digital Goods and Posted Prices

- When starting a mechanism-design or auction paper, first look at nearby
  formalized papers and `EconCSLib/MechanismDesign` for proof moves that should
  become reusable EC infrastructure. Build the reusable layer during the paper
  proof when it directly helps the active theorem and is likely useful for
  another auction/mechanism paper.
- For auction papers, attack the named theorem through the shortest faithful
  model level. Finite bidder models are often right for digital goods, but do
  not build a finite analogue as ritual if the paper statement or proof closes
  more directly through a certificate, threshold characterization, or
  expectation interface.
- Prove truthfulness at the threshold-rule level: if the threshold offered to
  bidder `i` is independent of `i`'s report, accepting iff bid exceeds that
  threshold is DSIC.
- Instantiate random-sampling or market-price auctions by proving the relevant
  own-bid-independence lemma.
- For fixed-price benchmarks, define a finite bidder-value candidate benchmark
  early. Reduce arbitrary feasible prices to bidder-value prices using the
  minimum accepted bidder value: raising to that value preserves the sale count
  lower bound and weakly increases revenue.
- For random-sampling digital-goods auctions, first prove the deterministic
  cross-sample threshold mechanism truthful for an arbitrary fixed partition;
  only after that add probability over partitions and revenue approximation.
- For weighted-pairing or selected-pair auction lower bounds, write the
  expected-payment/revenue formula as a concrete finite double sum first. When
  the proof keeps only same-bin or otherwise selected ordered pairs, define the
  selected pair index type and embed it injectively into the full pair index;
  then compare sums with `FiniteSum.sum_le_sum_of_injective_nonneg`. This is
  faster and more auditable than repeatedly expanding the full auction sum.
- For bucket/bin auction proofs, prefer actual `Finset` buckets over abstract
  pre-ranked arrays once the algebraic bridge is stable. Use a finite-ranking
  helper to derive value-sorted ranks, within-bin membership, image equality,
  and injectivity; use subtype/finset wrappers to derive high-low pair
  injections from disjoint bucket halves.
- For dyadic partition arguments, make the partition theorem tolerate empty
  bins. Canonical power-of-two ranges often include empty buckets, and requiring
  every bin to be nonempty forces irrelevant side proofs. Bound each empty bin
  by benchmark nonnegativity and each nonempty bin by the usual fixed-price
  floor argument.
- When a binning proof naturally has a classifier `bucketOf : Agent -> Bucket`,
  define buckets as classifier fibers. Then prove coverage by swapping sums over
  agents and buckets and using a singleton indicator sum; this avoids carrying
  manual disjointness and partition assumptions through every theorem.
- For dyadic largest-bucket arguments such as `|M| t = Ω(F)`, formalize the
  proof as a finite geometric-tail recurrence (`tail_j <= mass_j + tail_{j+1}/2`)
  plus a largest-total-bucket-to-floor-mass bridge. This is faster and more
  auditable than repeatedly unfolding all powers-of-two buckets in the main
  auction theorem.
- When the paper's dyadic tail starts at the fixed price, set the tail base to
  the price itself if that is faithful. This can remove factor-two slack from
  the winner-count bridge and make the "largest bucket has at least two
  bidders" contradiction close cleanly.
- For GHW-style `F >= 2h` largest-bucket size claims, prove the contrapositive
  with a strict finite geometric-tail lemma: if the largest dyadic bucket has
  at most one bidder, every bucket mass is at most `h`, so the finite dyadic
  tail is strictly below `2h`, contradicting `F >= 2h`.
- For paper statements involving `log h` dyadic bins, avoid fighting
  `Real.log` until the analytic endpoint truly needs it. A faster faithful
  route is often to take a natural-number log certificate such as
  `values i <= 2^(m+1)`, construct the `m+1` factor-two bins by induction on
  powers of two, and state the theorem with the explicit hypothesis
  `(m+1 : ℝ) <= s^2` or the relevant log-bound certificate.
- In weighted-pairing Theorem 7.2-style proofs, keep the fixed-price tail base
  separate from the selected largest bucket's floor. The fixed-price bound uses
  the bucket containing the price (`p <= 2 * baseFloor`) to count winners, while
  the high/low rank split uses the selected bucket floor `t`; forcing these to
  be the same creates unnecessary and non-paper assumptions.
- For repeated-bid tightness examples, model the actual population with
  dependent finite types such as `Sigma fun level => Fin (count level)` plus a
  separate `Fin s` top block. Prove the source's bookkeeping facts first
  (per-level total mass, total bid value, top-price fixed-price revenue, and
  classifier revenue split) before attacking the raw expected-payment
  inequalities.
- When a theorem's proof only needs a size/value precondition in one case split,
  derive it inside that branch instead of assuming it globally. For GHW-style
  arguments, `F <= T/s`, `F >= 2h`, and `2 <= s` give the `4h <= T` precondition
  for the Theorem 7.1 branch, while the largest-bucket branch should not inherit
  that extra assumption.
- Use a nonnegative offer-price wrapper around finite candidate prices so
  no-positive-transfer and expected-revenue nonnegativity proofs do not inherit
  infeasible negative candidate values from empty samples.
- When a finite candidate benchmark is positive and all bidder values are at
  least one, prove the selected candidate offer price is at least one before
  entering dyadic-bucket arguments. This avoids carrying an arbitrary
  benchmark-attaining price and ties the paper-facing `F^(2)` theorem directly
  to the reusable finite-candidate benchmark API.
- For deterministic single-parameter lower bounds, avoid starting with a real
  infimum unless the theorem truly needs it. In a fixed-other-bids offer slice,
  prove the fast DSIC atoms first: any two winning reports pay the same price;
  if a lower report wins then higher reports win; and if a higher report loses
  then lower reports lose. When a winning report exists, the common winning
  payment itself is the critical price: reports below it lose by feasibility,
  reports above it win by truthfulness, and the boundary may be open or closed.
- When lifting a deterministic offer-slice characterization back to a full
  digital-goods auction, define the induced fixed-other-bids offer once. Prove
  `LosersPayZero` from IR plus no-positive-transfers, use binary allocation to
  identify offer utility with the original auction utility, and then apply the
  offer-slice theorem. This is faster and cleaner than re-proving the critical
  price argument inside the full auction model.
- For binary deterministic bid-independent lower bounds, formalize arbitrary
  threshold prices directly before specializing to the paper's two-price WLOG.
  Classifying an offer as "high" when it is above the low value `1` proves the
  same adversarial transition and avoids spending proof effort on a separate
  normalization argument.
- When a paper's bid-independent auction is anonymous and takes a set/multiset
  of other bid values, bridge it to a count-threshold theorem by defining a
  canonical erased-bid representation for the restricted input family (for
  example, a list with all high values followed by all low values). This closes
  the paper's anonymous binary restriction without pretending it covers a
  stronger identity-aware threshold model.
- When moving between count-threshold and anonymous erased-list models on
  binary values, define the list rule by counting high values and low `1`
  values in the erased list, then prove it agrees on the canonical
  repeated-value list. This is usually faster and more source-faithful than
  carrying an opaque representation hypothesis through every downstream
  theorem.
- For ranked-auction telescoping proofs with terms like `V_j = b_j * (n-j)`,
  prove `V_j <= F` once from the actual sorted bid profile and fixed-price
  benchmark. Use the upper-rank finset of bidders with rank at least `j` to
  show price `b_j` has at least `n-j` winners, then feed that feasible price to
  the benchmark API. This removes a repetitive certificate hypothesis from the
  main revenue theorem.
- In ranked-auction Theorem 8.2-style proofs, do not keep adjacent monotone win
  probabilities as a primitive if the paper gives the two adjacent truthfulness
  comparisons. Prove `p_j <= p_{j+1}` by applying the Lemma 8.1 algebra to the
  low-value and high-value adjacent deviations, with only `p_0 = 0` plus
  nonnegativity of the first real win probability for the dummy endpoint. Keep
  these adjacent assumptions bounded to `j+1 < n`; if a helper asks for all
  natural indices, add the bounded finite-sum variant instead of fabricating
  out-of-range comparisons.
- When a lower-bound construction returns a feasible benchmark lower bound,
  strengthen it to the actual benchmark before declaring the paper endpoint
  closed. For finite candidate fixed-price benchmarks this usually means
  proving the constructed prices (`1` and the high value `H` in two-value GHW
  inputs) are feasible and then replacing the abstract certificate by the
  benchmark itself.
- If a finite benchmark API requires `[Nonempty Agent]` but a theorem quantifies
  over counts that may be zero, introduce a small paper-specific benchmark
  wrapper with an explicit empty case. Then prove all constructed witnesses are
  nonempty locally. This avoids leaking typeclass witnesses into the
  paper-facing statement.

## GSP and Position Auctions

- Start with `PositionOutcome`: per-click payments, utility, revenue, welfare,
  and feasibility.
- A concrete non-truthfulness witness is a good first theorem before building a
  generic bid-sorting mechanism and equilibrium comparisons.
- Use local envy-freeness as an outcome-level certificate for "no profitable
  assigned-slot deviation" before proving full Nash equilibrium of a sorted GSP
  mechanism.

## Combinatorial Auctions

- Reuse the fair-division bundle/allocation layer. Keep feasibility separate
  from direct mechanisms because approximation algorithms may leave goods
  unallocated.
- For single-minded bidders, define bundle-containment valuations before proving
  greedy allocation or critical-value payment theorems.
- Prove pairwise-disjoint accepted-set feasibility separately from greedy
  optimality; this lets the greedy algorithm theorem focus on acceptance
  invariants and critical-price monotonicity.

## General Mechanism Wrappers

- Define the paper's scalar functions exactly (`f`, `g`, `h`, utilities,
  welfare), prove algebraic equivalences to existing mechanism predicates, then
  prove the theorem from a small payoff/crossing certificate.
- When approximation proof is too large for the current pass, package it as a
  named certificate whose statement is exactly the benchmark/revenue inequality
  needed by the paper-facing theorem.
