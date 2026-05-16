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
- For admissions/testing strategic-threshold games, separate payoff
  threshold algebra from endogenous equilibrium existence. First prove the
  binary action payoff cutoff using the displayed probability law and inverse
  CDF, then add a paper-facing wrapper that expands any projected Gaussian
  scale into the source precision expression. Leave global fixed-point or
  school-threshold uniqueness as the next explicit seam rather than hiding it
  inside the cutoff lemma.
- For strategic threshold uniqueness proofs, strengthen weak cutoff
  best-response statements to strict payoff order away from the cutoff before
  attacking the fixed point. The reusable route is: strict inverse-CDF tail
  lemmas in `StandardGaussianQuantileAPI`, strict payoff/probability algebra,
  then a paper-facing theorem saying apply strictly dominates above the cutoff
  and not applying strictly dominates below it.
- For two-school strategic application regions, define the incremental payoff
  explicitly before proving best response: below the fallback school's cutoff
  the value is the preferred-school value, while above it the incremental value
  is the value difference. Prove the low/high cutoff region iff nonnegative
  incremental payoff, then separately prove the region indicator pointwise
  maximizes the binary apply/not-apply payoff.
- To prove uniqueness of a threshold/region strategy, first prove strict
  payoff signs away from every cutoff and then assume only the paper's
  tie-breaking convention at cutoff points. Split on the region boundary
  predicates, force the strategy by pointwise best-response inequalities in
  strict branches, and use the tie-breaking hypotheses only in equality cases.
- For school capacity fixed points, separate the scalar cutoff theorem from the
  probabilistic applicant-mass formula. First prove a reusable theorem that a
  continuous strictly decreasing applicant-mass function with end limits
  `totalMass` at `-∞` and `0` at `+∞` has a unique capacity cutoff and sublevel
  region. Then instantiate continuity, monotonicity, and limits from the
  paper's Gaussian or strategic applicant-mass expression.
- For strategic admissions cost-threshold arguments, do not hide the
  intermediate-value step inside an opaque certificate. Prove or reuse a
  one-dimensional decreasing-crossing theorem first: a continuous strictly
  decreasing merit term with opposite endpoint comparisons gives a positive
  threshold and exact weak/strict side characterizations. In `EconCSLib` this
  is the role of
  `exists_threshold_of_continuous_strictAntiOn_Icc_crossing` and
  `exists_threshold_le_of_continuous_strictAntiOn_Icc`. When the source proof
  uses an actual cost interval such as `[0,v]`, prefer the interval theorem
  `exists_threshold_of_continuous_strictAntiOn_Icc_crossing_interval` or the
  paper wrapper over normalizing to `[0,1]` unless normalization makes the
  concrete algebra easier.
- If the source derives cost-monotonicity indirectly, keep that structure in
  Lean. Prove the cost-to-cutoff map is continuous/strictly increasing, prove
  the cutoff-to-merit map is continuous/strictly decreasing, and compose them
  via `continuousOn_comp_of_mapsTo`, `strictAntiOn_comp_strictMonoOn`, or the
  paper wrapper
  `paper_proposition5_cost_merit_continuous_strictAntiOn_of_cutoff_strictMono`.
  This is usually faster and more auditable than assuming a black-box
  cost-to-merit monotonicity fact.
- For two-school full-test application payoffs, encode the displayed CDF
  expression first and prove monotonicity directly from signs. A typical term
  has negative CDF coefficients, while each standardized cutoff
  `(q_i - q) / scale` strictly decreases in projected skill `q`; strict CDF
  monotonicity plus `0 < v2 < v1` closes the "student strategy is threshold
  form" monotonicity claim before any school fixed-point work.
- When the paper solves an indifference equation with an inverse CDF, first
  prove the algebraic CDF equation from the zero-payoff equation, then apply the
  quantile API with the probability-domain premise explicit. Do not spend time
  deriving `(0,1)` membership from economic assumptions until the formula
  theorem itself is green; expose that domain as the next paper-facing
  obligation.
- To prove a cutoff increases in cost, use zero comparison and strict payoff
  monotonicity rather than differentiating the implicit inverse-CDF formula.
  Since cost usually enters as `-c`, evaluate the higher-cost payoff at the
  lower-cost zero to get a negative value, then strict monotonicity in skill
  forces the higher-cost zero to lie to the right.
- After proving a strategic payoff is continuous and strictly increasing, use a
  generic crossing lemma before specializing tail limits. The reusable theorem
  `existsUnique_zero_and_nonneg_iff_of_continuous_strictMono_crossing` turns
  one negative payoff point and one positive payoff point into a unique cutoff
  and an exact nonnegative upper-threshold region.
- When a strategic proof says a mass inequality is "equivalent" to a cutoff
  case, check whether the mass is simply a strictly antitone upper-tail
  function evaluated at the cutoff. If so, prove a tiny paper-facing bridge
  with `StrictAnti.lt_iff_gt`: `M = K cutoff` gives
  `M < K reference ↔ reference < cutoff`, and
  `M > K reference ↔ cutoff < reference`. This is much faster than expanding
  Gaussian integrals or tail formulas again, and it keeps the paper statement
  auditable.
- When a two-group strategic proof is a source-level case split ("no group
  triggers the cutoff case", "both groups trigger it but that is impossible",
  "only group A triggers it", "only group B triggers it"), first package that
  logic as an exact-one propositional bridge. Then plug in the economic
  qualifiers and mass/cutoff translations separately. This avoids duplicating
  symmetric case analysis inside every paper-facing objective theorem.
- When a school-deviation objective premise includes a displayed weighted
  academic-merit inequality plus a separate mass feasibility condition, split
  the bridge into bookkeeping facts instead of assuming the whole iff. First
  rewrite each objective value to the source weighted-merit expression, carry
  the mass feasibility hypothesis separately, and add a no-tie premise if the
  source uses a strict inequality but the game objective is weak preference.
  Then compose that smaller bridge into the paper-facing equilibrium wrapper.
- For strategic admissions equilibrium theorems that are still certificate
  based, make the certificate target source-shaped before doing fixed-point
  work. Define the paper's displayed inequalities, exactly-one-group clauses,
  policy-pair notation, and threshold-mass functions as Lean `Prop`/`def`
  declarations, then let the certificate prove the concrete game satisfies
  those definitions. This makes the human-facing theorem auditable and prevents
  opaque fields like `subFullEquilibriumIff : Prop` from hiding whether the
  Lean statement actually matches the paper.
- For two-school, two-policy admissions games, prove the normal-form
  unilateral-deviation bridge before the source inequalities. Each candidate
  pair `(P_sub,P_full)`, `(P_full,P_sub)`, and `(P_full,P_full)` should reduce
  to the two objective comparisons obtained by switching one school while
  holding the other fixed. Then connect the paper's analytic inequalities to
  those objective comparisons.
- Audit existential cost-boundary statements before treating them as substantive
  strategic conclusions. If a theorem only says there exist positive functions
  characterizing an equilibrium region, the bare existential may be provable by
  case-splitting on the equilibrium predicate and choosing artificial constant
  boundaries. Record that as an abstract statement-level closure, but keep the
  economically meaningful task separate: derive the intended boundary functions
  from continuity, monotonicity, and the concrete strategic fixed point.
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
- Once the natural-number dyadic certificate is closed, add the paper-facing
  real-log wrapper as a thin theorem rather than refactoring the bin proof.
  For base-two logs over normalized bids, set `m = Nat.ceil (Real.logb 2 h)`,
  use `Real.logb_le_iff_le_rpow` and `Real.rpow_natCast` to get
  `h <= 2^m <= 2^(m+1)`, then use `Nat.ceil_lt_add_one` to bound
  `m+1 <= Real.logb 2 h + 2`. This keeps analytic imports narrow
  (`Mathlib.Analysis.SpecialFunctions.Log.Base`) and preserves a green
  dyadic theorem if exact paper log constants are still caveated.
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
- Prefer payment-form ranked revenue wrappers before introducing conditional
  expected costs. Define `gain i = p_{i+1} * b_i - payment_i`; the high-value
  adjacent truthfulness inequality gives the recursion
  `gain_i + p_{i+1}(b_{i+1}-b_i) <= gain_{i+1}`, while the low/high adjacent
  payment inequalities and strict adjacent ranked bids give monotone win
  probabilities. This usually removes an artificial `expectedCost` variable
  from the paper-facing Theorem 8.2 seam and leaves only the concrete
  randomized-auction DSIC-to-ranked-payment bridge.
- Once a ranked-payment wrapper is green, stop adding more conditional algebra
  variants. The next useful proof work is the model bridge: define the concrete
  anonymous/sorted-bid randomized auction interface, prove its expected revenue
  decomposes as the ranked payment sum, and derive the adjacent payment-form
  truthfulness inequalities from DSIC. Record that exact bridge in the README
  if stopping before it is proved.
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

## Dynamic Games, PBE, and Schedule Certificates

- For long dynamic-game proofs, keep a theorem-specific scratch plan beside the
  paper files. Record current Lean endpoints, the exact mathematical gap, the
  next bridge lemmas, why they should be true, and which assumptions are genuine
  source assumptions versus temporary certificate fields. When Lean gets too
  low-level, write the informal recurrence, induction, or history construction
  first, then translate only the stable pieces into named Lean declarations and
  audit wrappers.
- In EOS-style finite dropout/PBE proofs, exact-drop histories, finite
  completed-rank wrappers, core-vs-full source-completion certificates, and
  derived-outcome bridges make the extensive-form gap visible while still
  allowing verified algebra to accumulate. If a scratch proof shows that some
  certificate fields are consequences of other fields, formalize the smaller
  core certificate and a derived bridge before continuing.
- When a source proof uses local payoff comparisons as the sequential
  rationality step, promote the raw algebra into named payoff definitions and a
  small best-response predicate before proving the full dynamic-game
  obligation. In EOS Theorem 8, exposing continue payoff, drop payoff, and the
  finite `B*` one-step best-response theorem made the remaining
  belief/sequential-rationality lift auditable.
- If the source proof uses strict exclusion directions, add an off-threshold
  strict wrapper pairing the strict payoff inequality with the strategy's
  actual drop/not-drop action. If behavioral uniqueness depends on tie-breaking
  at an indifference threshold, make tie-breaking a named predicate and prove a
  characterization theorem from local best response plus tie-breaking to the
  paper cutoff rule.
- When a PBE predicate existentially packages a belief and a
  sequential-rationality proof, do not keep behavioral facts as opaque
  "every PBE behaves this way" obligations if the source proof is really about
  sequential rationality. Add a certificate proving local best response and
  tie-breaking from `isSequentiallyRational`, then unpack the PBE witness in a
  thin bridge.
- If the source proof defines sequential rationality by local deviations,
  sharpen the certificate to an iff between `isSequentiallyRational` and the
  audited local optimality/tie-breaking predicates. The reverse direction
  should lift the named strategy's local proof to game-level sequential
  rationality; the forward direction should replace opaque arbitrary-PBE
  behavior fields. If the paper says the best response is belief-independent,
  add an ex-post local-deviation certificate layer and conversion lemmas to the
  local-deviation core and one-sided source steps.
- For recursive or hard-to-audit paper-facing premises such as clock-sorted
  finite schedules, add `nil`, `cons`, `singleton`, pair, and
  append-singleton helpers so humans can verify concrete instances by local
  inequalities. If a finite schedule theorem asks separately that the completed
  set is contained in the schedule, add an all-scheduled constructor for the
  common case `completed = scheduledRanks.toFinset`.
- When a concrete history condition is local to realized transitions, make it a
  first-class history object instead of a global predicate over all possible
  states. For exact schedules, add a conversion to the annotated history object
  and a terminal-history certificate constructor. This gives the audit path:
  clock-sorted schedule -> exact schedule -> annotated finite history ->
  terminal records/source certificate.
- If a sharper concrete-history certificate is introduced, mirror the ordinary
  certificate stack with forgetful constructors and obligation ledgers:
  terminal-history certificate, terminal/dynamic certificate, core source
  certificate, full source certificate, finite source certificate, and direct
  paper-facing endpoints.
- For nonempty finite schedules, expose an append-singleton final-clock lemma:
  if the schedule is `scheduledPrefix ++ [lastRank]`, the final clock is the
  last scheduled threshold. Then provide endpoints whose terminality premise
  compares unscheduled thresholds to that last threshold instead of to a
  recursively computed final state.
- When recursive schedule sortedness mixes initial-clock and adjacent-threshold
  obligations, split out an adjacent-threshold sorted predicate. Prove a bridge
  from initial-clock-plus-threshold-sorted to the recursive predicate and
  discharge the initial-clock inequality automatically for cold starts.
- Expose intermediate certificate constructors as first-class definitions, not
  only final theorem endpoints. If a terminal-dynamic certificate is built from
  a concrete strategy-consistent terminal history, expose the terminal-history
  behavior certificate and direct facts such as scheduled-rank terminal records
  and final-state active iff unscheduled.
- When the final source boundary combines source PBE semantics with an exact
  terminal history, create a single bundled source-completion certificate that
  proves the final unique-PBE conclusion. If exact terminal-history completion
  is only finite, expose a finite analogue with the completed set and
  inactive-on-completed proof as fields, and derive the finite
  unique-PBE terminal-record conclusion from it.
- If a source-shaped checker already instantiates the ex-post/local-deviation
  semantics, add constructors from exact histories and exact schedules into the
  finite bundled certificate, plus an all-scheduled variant. If an adjacent
  source-obligation layer already has a sorted-schedule endpoint, add a direct
  endpoint from the sharper ex-post/local-deviation layer and an all-scheduled
  specialization. For small concrete schedules, mirror singleton/pair helpers
  at that sharper layer.
- For source-completion certificates, expose obligation-conjunction theorems
  for each important layer. The full certificate should list all source
  obligations, while core, one-sided, ex-post, sequential-rationality,
  one-step/tie-break, and local-deviation certificates should list only their
  minimized obligations. Also expose direct downstream endpoints from reduced
  certificates to named-strategy PBE, PBE strategy equality, the cutoff/action
  rule, unique PBE, outcome equality, and compact paper conclusions, so audit
  files can cite one theorem from the minimized source obligation.
- For exact finite schedules, expose deterministic-final-state facts:
  scheduled ranks have terminal records equal to their threshold, and from an
  all-active initial state the active ranks are exactly the unscheduled ranks.
  If an endpoint already contains terminal-record conclusions but its name only
  says `exists_unique_pbe`, add a paper-facing alias whose name explicitly says
  `with_terminal_record_conclusion`.
- When a paper theorem includes a continuity restriction on a strategy formula,
  formalize continuity of the numeric policy formula itself, not just
  monotonicity or affine algebra; expose both scalar and indexed/update forms
  if the theorem is rank-indexed.
- When a theorem states "same payoff" and the formalization already proves slot
  and payment equality, add a utility-extensionality bridge and a direct
  paper-facing utility-equality endpoint so reviewers do not have to unfold the
  quasilinear utility definition. If the theorem has both all-rank and finite
  completed-rank routes, expose the payoff endpoint for both routes.
- When a source model uses a convention such as an empty history value, add a
  named theorem that rewrites the general formula under that convention, plus
  the indexed specialization if the theorem is rank-indexed.
- When strict monotonicity is used in a source uniqueness argument, add the
  corresponding injectivity theorem so later uniqueness proofs can cite the
  identification property directly.
- If the source proof uses a named scalar such as `q`, expose source-proof-line
  aliases for the defining formula, expected interval, endpoint, monotonicity,
  and continuity checks after proving the lower-level algebra.
- At abstract game-interface layers, expose payoff-equality bridges from
  same-allocation/same-payment fields before building more specialized
  endpoints. Also expose outcome-equality-to-payoff-equality bridges when
  stronger outcome equality is already the common endpoint.
- When a certificate field captures a paper phrase such as "best response
  regardless of beliefs," expose a direct theorem with that conclusion instead
  of leaving reviewers to inspect the field projection manually. When final
  theorem objects wrap a source certificate, lift the endpoint to those final
  objects too.
- If an iff endpoint converts source sequential rationality into a local
  paper-facing predicate, expose the direct theorem discharging that predicate
  from the named-strategy best-response obligation. When the only use of a
  belief argument is to instantiate a belief-independent result, expose a
  `[Nonempty Belief]` citation form. When a paper-facing strategy is named,
  expose the named-strategy `for all beliefs` iff source-local-predicate
  endpoint, not only the arbitrary-strategy iff.
