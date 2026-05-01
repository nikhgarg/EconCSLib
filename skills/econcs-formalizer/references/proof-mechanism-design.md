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
- For dyadic largest-bucket arguments such as `|M| t = Ω(F)`, formalize the
  proof as a finite geometric-tail recurrence (`tail_j <= mass_j + tail_{j+1}/2`)
  plus a largest-total-bucket-to-floor-mass bridge. This is faster and more
  auditable than repeatedly unfolding all powers-of-two buckets in the main
  auction theorem.
- Use a nonnegative offer-price wrapper around finite candidate prices so
  no-positive-transfer and expected-revenue nonnegativity proofs do not inherit
  infeasible negative candidate values from empty samples.
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
