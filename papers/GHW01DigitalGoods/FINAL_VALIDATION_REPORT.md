# Final Validation Report: Competitive Auctions

## 1. Human Verdict

- Lean formalization status: `formalized`.
- Human dashboard status: 0/19 rows reviewed, 19 unreviewed, 0 stale, 0
  mismatch. No human review entries have been saved yet.
- Paper correctness verdict: the later journal version resolves the only
  substantive source ambiguity found here. The broad preliminary Theorem 8.2
  wording is false as a weak DSIC/bid-independent statement; the journal
  monotone-auction statement is the source of truth for Section 8.2.
- Qualitative proof verdict: the formalization follows the paper's section
  structure. Section 8.2 uses a direct finite PMF layer-cake proof from the
  journal raw-CDF monotonicity condition instead of assuming a common-seed
  coupling. Section 9.3 derives the erased-list/list-price bridge internally
  from the paper's set-of-bids convention and Lemma 9.2.
- Lean footprint: 598 lines across paper-local `.lean` files; 290 lines and 20
  declarations in `PaperInterface.lean`; 19 dashboard rows.

## 2. Source and Scope

- Primary formalized source: *Competitive Auctions*, later journal version, by
  Andrew V. Goldberg, Jason D. Hartline, Anna R. Karlin, Michael Saks, and
  Andrew Wright.
- Historical numbering source: *Competitive Auctions and Digital Goods* by
  Goldberg, Hartline, and Wright, InterTrust technical report STAR-TR-99-01,
  revised November 2000. Folder name and audit aliases keep the SODA
  2001/InterTrust numbering as a crosswalk.
- Journal PDF:
  https://users.eecs.northwestern.edu/~hartline/papers/auctions-journal.pdf
- Historical PDF mirror:
  https://www.cs.miami.edu/home/burt/learning/Csc597.052/docs/goldberg.pdf
- Local source cache: tracked text cache `GHW01DigitalGoods.txt`. The ignored
  source PDF may be absent from public checkouts; it was not present for this
  validation pass.
- Web-source note: a 2026-06-01 search did not find public TeX/source. The
  journal version controls where it refines the preliminary report.
- Human-facing Lean file: `PaperInterface.lean`.
- Importable audit ledger: `PostPaperAudit.lean`.
- DAG artifacts: `DependencyDAG.tex`; rendered local ignored
  `DependencyDAG.pdf` was visually inspected.

## 3. What Has Been Proven

The paper's digital-goods mechanism definitions, truthful threshold mechanisms,
fixed-price benchmarks, random-sampling bounds, weighted-pairing bounds,
randomized-auction revenue upper bound, deterministic bid-independent lower
bound, deterministic truthfulness threshold structure, and deterministic
truthful lower bound are all represented by compiling paper-facing endpoints.

Corollary 4.2 and Theorem 6.2 no longer take external model witnesses:
truncation and ranked top-prefix sampling are constructed internally. Theorem
8.2 no longer takes the old coupled-outcome model as a public assumption.
Theorem 9.3 no longer takes an anonymous erased-bid/list-price representation
as a public assumption; it is derived from the source-shaped deterministic
auction model.

## 4. Paper Definitions Checked

- Digital-goods revenue: total payments collected from all bidders.
  Lean: `PaperInterface.revenue`.
- Dominant-strategy truthfulness: truthful reporting weakly dominates any
  single-agent report deviation.
  Lean: `PaperInterface.truthful`.
- Single-price revenue and fixed-price benchmark.
  Lean: `PaperInterface.singlePriceRevenue`,
  `PaperInterface.fixedPriceBenchmark`.
- Two-winner fixed-price benchmark `F^(2)`.
  Lean: `PaperInterface.twoWinnerBenchmark`.
- Total bid value `T`.
  Lean: `PaperInterface.totalValue`.
- Weighted-pairing expected revenue.
  Lean: `PaperInterface.weightedPairingRevenue`.

## 5. Named Theorem Statements Checked

- Theorem 4.1, cached line 359: high-value profiles satisfy the logarithmic
  fixed-price lower bound. Lean: `theorem4_1_high_value`; audit:
  `audit_theorem4_1_high_value`. Status: `formalized`.
- Corollary 4.2, cached line 301: cutoff truncation gives the factor-four
  fixed-price lower bound. Lean: `corollary4_2_fixed_price_lower_bound`; audit:
  `audit_corollary4_2_fixed_price_lower_bound`. Status: `formalized`.
- Lemma 6.1, cached line 428: fair-coin lower-tail estimate. Lean:
  `lemma6_1_fair_coin`; audit: `audit_lemma6_1_fair_coin`. Status:
  `formalized`.
- Theorem 6.2, cached line 479: random sampling auction revenue guarantee.
  Lean: `theorem6_2_random_sampling`; audit:
  `audit_theorem6_2_random_sampling`. Status: `formalized`.
- Theorem 7.1, cached line 563: weighted pairing gets the logarithmic guarantee
  under `4h <= T`. Lean: `theorem7_1_weighted_pairing`; audit:
  `audit_theorem7_1_weighted_pairing`. Status: `formalized`.
- Theorem 7.2, cached line 626: weighted pairing competes with `F^(2)` under
  `F^(2) >= 2h`. Lean: `theorem7_2_weighted_pairing_benchmark`; audit:
  `audit_theorem7_2_weighted_pairing_benchmark`. Status: `formalized`.
- Lemma 8.1, cached line 747: truthfulness implies monotone win probabilities.
  Lean: `lemma8_1_truthful_monotone`; audit:
  `audit_lemma8_1_truthful_monotone`. Status: `formalized`.
- Theorem 8.2, cached line 833 plus journal correction: monotone truthful
  randomized auctions have expected revenue at most `F`. Lean:
  `theorem8_2_truthful_revenue_upper_bound`; audit:
  `audit_theorem8_2_truthful_revenue_upper_bound`. Status: `formalized` for
  the journal statement. The weak preliminary reading is refuted by
  `theorem8_2_weak_truthful_counterexample` and
  `audit_theorem8_2_weak_truthful_counterexample`.
- Theorem 9.1, cached line 979: bid-independent auctions have a lower-bound
  witness. Lean: `theorem9_1_bid_independent_lower_bound`; audit:
  `audit_theorem9_1_bid_independent_lower_bound`. Status: `formalized`.
- Lemma 9.2, cached line 1105: truthful deterministic binary auctions admit
  threshold offers. Lean: `lemma9_2_threshold_domination`; audit:
  `audit_lemma9_2_threshold_domination`. Status: `formalized`.
- Theorem 9.3, cached line 1100: deterministic truthful auctions have the
  lower-bound witness. Lean:
  `theorem9_3_deterministic_truthful_lower_bound`; audit:
  `audit_theorem9_3_deterministic_truthful_lower_bound`. Status:
  `formalized`.

## 6. Additional Assumptions Beyond Paper

None. The paper-facing source models package the paper's own conventions:
finite bidder profiles, nonnegative values/prices where the auction model
requires them, journal raw-CDF monotonicity for Section 8.2, and anonymous
set-of-bids/masked-vector behavior for Section 9.3.

## 7. Proof-Strategy Deviations

- Theorem 8.2 is checked against the journal monotone-auction statement, not
  the overly broad preliminary sentence. Lean also proves the concrete
  counterexample to the broad reading.
- Theorem 8.2 proves the revenue recursion directly from raw marginal CDF
  inequalities by finite PMF layer-cake algebra. The common-seed coupled model
  remains only as reusable support/audit material.
- Theorem 9.3 uses a source-shaped deterministic auction model for the paper's
  `A_i(B_i^x)` convention, then derives erased-list relabeling and list-price
  behavior internally before applying Lemma 9.2.

## 8. Proof Tricks Worth Reusing

- Search for later paper versions and public source archives before deciding
  whether a Lean field is an extra assumption; later journal versions may
  clarify anonymity, tie-breaking, or corrected theorem scope.
- Prefer source-shaped final models over proof-adapter structures in
  `PaperInterface.lean`, then audit broad paper-module exports so old adapters
  do not reappear as public endpoints.
- For finite randomized digital-goods auctions, raw CDF monotonicity can often
  be pushed directly to acceptance probabilities and surplus recursions using
  finite PMF layer-cake sums.

## 9. Library Lift Pass

Reusable auction material already lives in
`EconCSLib/MechanismDesign/Auctions/MainTheorems.lean`. A future second-paper
use case could factor the finite PMF layer-cake surplus lemmas behind Theorem
8.2 into a smaller stochastic-ordering API; no risky extraction is needed for
this closeout.

## 10. DAG Audit

`DependencyDAG.tex` was updated to identify the journal source, keep the
InterTrust/SODA numbering crosswalk, distinguish theorem/corollary nodes from
lemma and model-layer nodes, and remove implementation-only wording from green
nodes. The DAG was rendered from the paper folder and visually inspected as a
PNG conversion of `DependencyDAG.pdf`; no node overlap, legend overlap,
label-overlap, or arrow-through-text issue remained after rerouting the final
arrows.

Dashed edges in the DAG are paper-route/context links, not unresolved Lean
dependencies. There are no open or conditional DAG nodes.

## 11. Conditional Results and Remaining Gaps

None. All public paper endpoints discharge their bridge/adaptation work
internally. Older coupled-offer and proof-adapter declarations remain only as
auxiliary reusable-library/audit material.

## 12. Suspected Paper Errors or Inconsistencies

- Preliminary Theorem 8.2, read literally as weak truthfulness plus
  bid-independent pricing, is false. Lean records a two-bidder threshold
  counterexample earning `101` against fixed-price benchmark `100`.
- The journal version corrects the Section 8.2 scope by using monotone
  truthful randomized auctions. No other source inconsistency was found.

## 13. Validation Checks

- `lake build GHW01DigitalGoods`: passed.
- `lake build EconCSLib`: passed.
- Source named-result grep over `GHW01DigitalGoods.txt`: found Theorem 4.1,
  Corollary 4.2, Lemma 6.1, Theorem 6.2, Theorems 7.1--7.2, Lemma 8.1,
  Theorem 8.2, Theorem 9.1, Lemma 9.2, and Theorem 9.3.
- Placeholder/stale-status scan over the claimed paper/library/status files:
  no GHW theorem gap found. Generic repository workflow and skill references
  to partial papers remain for other papers.
- Dashboard cache refresh: passed.
- Dashboard precheck: 0 stale, 0 mismatch, 19 unreviewed rows. The
  paper-local `./review-dashboard.sh --check` reports the same data and exits
  nonzero only because the 19 human review entries are not yet saved.
- DAG render: `latexmk -pdf -g -interaction=nonstopmode -halt-on-error
  DependencyDAG.tex` passed from the paper folder. MiKTeX emitted read-only log
  warnings for its home cache, but produced the PDF successfully.
- Repository audit: `python3 scripts/audit_repository.py` passed with 0 errors
  and 33 warnings. The warnings are public-checkout packaging or unrelated
  paper review-slice/cache items, including the expected missing ignored source
  PDF for GHW01.
- `git diff --check`: passed.

## 14. Final Verdict

Completion status: `formalized`.

The GHW01 digital-goods folder now presents the journal-controlled source
statements through a compact paper interface and a source-numbered audit ledger.
The former Section 8.2 and 9.3 public proof-adapter assumptions have been
discharged or moved out of the paper-facing surface, and no named paper endpoint
remains conditional on an unproved model bridge.
