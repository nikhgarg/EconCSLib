# Final Validation Report: Competitive Auctions

## 1. Human Verdict

- Lean formalization status: formalized
- Human dashboard review status: 0/19 rows reviewed; 0 stale; 0 mismatches.
- Human summary: This only uses a few lines of code as its infrastructure has largely been elevated to the shared auctions library. The journal version is used as the corrected source for Theorem 8.2.

- Lean formalization status: `formalized`.
- Human dashboard status: 0/19 rows reviewed, 19 unreviewed, 0 stale, 0
  mismatch. No human review entries have been saved yet.
- Paper correctness verdict: the journal version is used as the corrected
  source for Theorem 8.2 and resolves the only substantive source ambiguity
  found here. The broad preliminary Theorem 8.2 wording is false as a weak
  DSIC/bid-independent statement; the journal monotone-auction statement is the
  source of truth for Section 8.2.
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
- Local source cache: ignored local text/PDF caches may be regenerated for
  source searches; they may be absent from public checkouts.
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

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def revenue | `revenue` | - Digital-goods auction revenue: total payments collected from all bidders. |
| def truthful | `truthful` | - Dominant-strategy truthfulness: truthful bidding weakly dominates replacing one agent's value report by any alternative report. |
| def singlePriceRevenue | `singlePriceRevenue` | - Single-price revenue at price `p`. |
| def fixedPriceBenchmark | `fixedPriceBenchmark` | - Fixed-price benchmark over bidder-value candidate prices, requiring at least `minWinners` winners. |
| def twoWinnerBenchmark | `twoWinnerBenchmark` | - Two-winner fixed-price benchmark `F^(2)`: the best single-price revenue selling to at least two bidders. |
| def totalValue | `totalValue` | - Total bid value `T = sum_i v_i`. |
| def weightedPairingRevenue | `weightedPairingRevenue` | - Expected revenue of the weighted-pairing auction. |
<!-- lean-derived-definitions:end -->

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

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem4_1_high_value | `theorem4_1_high_value` | - Theorem 4.1: high-value profiles have a logarithmic fixed-price lower bound. |
| theorem corollary4_2_fixed_price_lower_bound | `corollary4_2_fixed_price_lower_bound` | - Corollary 4.2: truncating bids below `h / n` and applying Theorem 4.1 gives the logarithmic fixed-price lower bound. |
| theorem lemma6_1_fair_coin | `lemma6_1_fair_coin` | - Lemma 6.1: fair-coin random sampling lower-tail estimate. |
| theorem theorem6_2_random_sampling | `theorem6_2_random_sampling` | - Theorem 6.2: random-sampling auction revenue guarantee for finite candidate benchmark inputs satisfying `alpha * h <= F`. |
| theorem theorem7_1_weighted_pairing | `theorem7_1_weighted_pairing` | - Theorem 7.1: weighted pairing gets a logarithmic guarantee when `4h <= T`. |
| theorem theorem7_2_weighted_pairing_benchmark | `theorem7_2_weighted_pairing_benchmark` | - Theorem 7.2: weighted pairing competes with the two-winner benchmark. |
| theorem lemma8_1_truthful_monotone | `lemma8_1_truthful_monotone` | - Lemma 8.1: truthfulness implies monotone own-bid allocation. |
| theorem theorem8_2_truthful_revenue_upper_bound | `theorem8_2_truthful_revenue_upper_bound` | - Theorem 8.2, journal version: every monotone truthful randomized offer auction's expected revenue is bounded by `F`. The source model records the journal CDF monotonicity condition on raw marginal offer laws; Lean discharges the finite... |
| theorem theorem8_2_weak_truthful_counterexample | `theorem8_2_weak_truthful_counterexample` | - Source-audit boundary for Theorem 8.2: weak truthfulness plus ordinary threshold pricing alone does not imply the paper's revenue upper bound. |
| theorem theorem9_1_bid_independent_lower_bound | `theorem9_1_bid_independent_lower_bound` | - Theorem 9.1: bid-independent auctions have a lower-bound witness. |
| theorem lemma9_2_threshold_domination | `lemma9_2_threshold_domination` | - Lemma 9.2: deterministic truthful binary auctions admit threshold offers. |
| theorem theorem9_3_deterministic_truthful_lower_bound | `theorem9_3_deterministic_truthful_lower_bound` | - Theorem 9.3: deterministic truthful auctions have a lower-bound witness. The source model supplies the paper's set-of-bids focused-outcome convention; erased-list relabeling and then Lemma 9.2's anonymous list-price representation are... |
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GHW01DigitalGoods --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| theorem corollary4_2_fixed_price_lower_bound | `corollary4_2_fixed_price_lower_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def fixedPriceBenchmark | `fixedPriceBenchmark` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem lemma6_1_fair_coin | `lemma6_1_fair_coin` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem lemma8_1_truthful_monotone | `lemma8_1_truthful_monotone` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem lemma9_2_threshold_domination | `lemma9_2_threshold_domination` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def revenue | `revenue` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def singlePriceRevenue | `singlePriceRevenue` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem4_1_high_value | `theorem4_1_high_value` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem6_2_random_sampling | `theorem6_2_random_sampling` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem7_1_weighted_pairing | `theorem7_1_weighted_pairing` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem7_2_weighted_pairing_benchmark | `theorem7_2_weighted_pairing_benchmark` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem8_2_truthful_revenue_upper_bound | `theorem8_2_truthful_revenue_upper_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem8_2_weak_truthful_counterexample | `theorem8_2_weak_truthful_counterexample` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem9_1_bid_independent_lower_bound | `theorem9_1_bid_independent_lower_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem9_3_deterministic_truthful_lower_bound | `theorem9_3_deterministic_truthful_lower_bound` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def totalValue | `totalValue` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def truthful | `truthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def twoWinnerBenchmark | `twoWinnerBenchmark` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def weightedPairingRevenue | `weightedPairingRevenue` | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:27Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Additional Assumptions Beyond Paper

None. The paper-facing source models package the paper's own conventions:
finite bidder profiles, nonnegative values/prices where the auction model
requires them, journal raw-CDF monotonicity for Section 8.2, and anonymous
set-of-bids/masked-vector behavior for Section 9.3.

## 8. Proof-Strategy Deviations

- Theorem 8.2 is checked against the journal monotone-auction statement, not
  the overly broad preliminary sentence. Lean also proves the concrete
  counterexample to the broad reading.
- Theorem 8.2 proves the revenue recursion directly from raw marginal CDF
  inequalities by finite PMF layer-cake algebra. The common-seed coupled model
  remains only as reusable support/audit material.
- Theorem 9.3 uses a source-shaped deterministic auction model for the paper's
  `A_i(B_i^x)` convention, then derives erased-list relabeling and list-price
  behavior internally before applying Lemma 9.2.

## 9. Proof Tricks Worth Reusing

- Search for later paper versions and public source archives before deciding
  whether a Lean field is an extra assumption; later journal versions may
  clarify anonymity, tie-breaking, or corrected theorem scope.
- Prefer source-shaped final models over proof-adapter structures in
  `PaperInterface.lean`, then audit broad paper-module exports so old adapters
  do not reappear as public endpoints.
- For finite randomized digital-goods auctions, raw CDF monotonicity can often
  be pushed directly to acceptance probabilities and surplus recursions using
  finite PMF layer-cake sums.

## 10. Library Lift Pass

Reusable auction material already lives in
`EconCSLib/MechanismDesign/Auctions/MainTheorems.lean`. A future second-paper
use case could factor the finite PMF layer-cake surplus lemmas behind Theorem
8.2 into a smaller stochastic-ordering API; no risky extraction is needed for
this closeout.

## 11. DAG Audit

`DependencyDAG.tex` was updated to identify the journal source, keep the
InterTrust/SODA numbering crosswalk, distinguish theorem/corollary nodes from
lemma and model-layer nodes, and remove implementation-only wording from green
nodes. The DAG was rendered from the paper folder and visually inspected as a
PNG conversion of `DependencyDAG.pdf`; no node overlap, legend overlap,
label-overlap, or arrow-through-text issue remained after rerouting the final
arrows.

The DAG uses closed dependency arrows only; it does not use the shared dashed
edge style, which can denote unresolved or conditional dependencies in other
paper diagrams. There are no open or conditional DAG nodes.

## 12. Conditional Results and Remaining Gaps

None under the source/version choice recorded above. Theorem 8.2 is the journal
raw-CDF monotone-offer theorem, not the false broad weak-DSIC reading. Theorem
9.3 is the deterministic truthful theorem under the paper's set-of-bids
focused-outcome convention. All bridge/adaptation work from those source-shaped
models is discharged internally. Older coupled-offer and proof-adapter
declarations remain only as auxiliary reusable-library/audit material.

## 13. Suspected Paper Errors or Inconsistencies

- Preliminary Theorem 8.2, read literally as weak truthfulness plus
  bid-independent pricing, is false. Lean records a two-bidder threshold
  counterexample earning `101` against fixed-price benchmark `100`.
- The journal version is used as the corrected source for Theorem 8.2, using
  monotone truthful randomized auctions. No other source inconsistency was
  found.

## 14. Validation Checks

- `lake build GHW01DigitalGoods`: passed.
- `lake build EconCSLib`: passed.
- Source named-result grep over the local text cache found Theorem 4.1,
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
  and 21 warnings. The warnings are public-checkout packaging or unrelated
  paper review-slice/cache items, including the expected missing ignored source
  PDF for GHW01.
- `git diff --check`: passed.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 19 rows; 19 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

Flagged rows:
- None.

## 15. Final Verdict

Completion status: `formalized`.

The GHW01 digital-goods folder now presents the journal-controlled source
statements through a compact paper interface and a source-numbered audit ledger.
The former Section 8.2 and 9.3 public proof-adapter assumptions have been
discharged or moved out of the paper-facing surface, and no named paper endpoint
remains conditional on an unproved model bridge.

- Completion status: formalized.
- Summary: This only uses a few lines of code as its infrastructure has largely been elevated to the shared auctions library. The journal version is used as the corrected source for Theorem 8.2.
