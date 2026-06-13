# Final Validation Report: MSVV07 AdWords

## 1. Human Verdict

- Lean formalization status: formalized.
- Human dashboard review status: 0/26 rows reviewed; 0 stale; 0 mismatches.
- LLM statement-translation audit: 26/26 dashboard rows match; the 10
  assumption-ledger rows also have current statement translations and
  statement-judge entries.
- Paper correctness verdict: no suspected paper error found.
- Qualitative proof verdict: the Balance/MSVV structure, Section 6/8
  extensions, and Theorem 9 lower-bound endpoint are exposed and compile. The
  paper-facing formulas and final source-section endpoints pass the current
  source-premise audit; certificate-heavy helper APIs remain internal proof
  infrastructure rather than dashboard targets.
- Lean footprint: 13,598 paper-local Lean lines, including 902 lines in
  `PaperInterface.lean` and 26 dashboard review rows.

<!-- transitive-source-premise-audit:start -->
### Axiom, Premise, And Source-Hygiene Audit

The current axiom/premise/source-hygiene audit passes for full-status provenance. It uses Lean-native #print axioms for transitive proof debt, expanded paper-facing signatures for visible premises, and source-assumption ledgers for any non-derived assumptions.

Current result: no unresolved hidden source-row or certificate premise remains in the paper-facing review surface.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

- Paper: *AdWords and Generalized Online Matching*.
- Source version: Journal of the ACM 54(5), 2007, Article 22, DOI
  `10.1145/1284320.1284321`; public author PDF:
  `https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf`.
- Lean folder: `papers/MSVV07AdWords`.
- Human-facing statement surface: `papers/MSVV07AdWords/PaperInterface.lean`.
- Audit ledger: `papers/MSVV07AdWords/PostPaperAudit.lean`, imported by the
  paper root.
- DAG artifacts: `papers/MSVV07AdWords/DependencyDAG.tex` and
  `papers/MSVV07AdWords/DependencyDAG.pdf`.

## 3. What Has Been Proven

The paper's finite AdWords model, budget feasibility, small-bids condition,
fractional LP benchmark, Balance/MSVV score and choice rule, Theorem 8
competitive-ratio guarantee, Section 6 extensions, Section 8 weighted-bid
extension, and Theorem 9 randomized-online lower bound are formalized.

Source-route Lemmas 1--7 are formalized as proof-audit endpoints supporting the
Theorem 8 route. They are not part of the compact dashboard surface because the
review surface is reserved for paper-facing formulas and final section/theorem
endpoints.

## 4. Paper Assumption Provenance

> Axiom/premise/source-hygiene audit update (2026-06-12): `assumption_match_llm.json` records per-premise judgments for this paper's `Assumptions.lean` ledger. Current result: 13/13 premises are judged source model primitives, derived representation conditions, or paper-statement conditions; 0 premises remain as partial-formalization boundaries.

Every paper-facing premise is routed through `MSVV07AdWords/Assumptions.lean`
and checked by `assumption_match_llm.json`. These are source model conditions
or finite-run conditions for Theorem 8 and the Section 6/8 extensions; none are
extra proof certificates.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_nonnegative_bids` | paper condition | AdWords bids are nonnegative revenue/payment amounts. |
| `assumption_full_distinct_query_history` | paper condition | Finite query history enumerates the instance for explicit-error accounting. |
| `assumption_epsilon_range` | paper condition | Small-bids error parameter is in `[0,1]`. |
| `assumption_alive_bidder_predicate` | paper condition | Section 6 next-price variant among alive bidders. |
| `assumption_next_highest_all_small_bids` | paper condition | All-bidders next-price effective bids satisfy small bids. |
| `assumption_next_highest_alive_small_bids` | paper condition | Alive-bidders next-price effective bids satisfy small bids. |
| `assumption_click_through_rates_probability_bounds` | paper condition | Click-through rates are probabilities. |
| `assumption_availability_predicate` | paper condition | Delayed-entry availability predicate for Section 6. |
| `assumption_weighted_bids_nonnegative_weights` | paper condition | Section 8 advertiser weights are nonnegative. |
| `assumption_weighted_effective_small_bids` | paper condition | Weighted effective bids satisfy small bids. |

Additional assumptions beyond the paper: none. Relevant finite-history,
nonnegative-bid, positive-budget, distinctness, and small-bids side conditions
appear explicitly in the Lean statements and in the provenance ledger above.

## 5. Proof-Strategy Deviations

- Theorem 8 is proved through finite Balance history accounting with an
  explicit small-bids error term, then wrapped as the paper-level limiting
  theorem.
- Section 6 multiple slots are represented by a source-shaped page-level model
  selecting the top `n_q` distinct feasible advertisers for each page.
- Theorem 9 uses a finite observed-prefix algorithm model; broader
  observed-prefix and integral-prefix support endpoints are kept out of the
  dashboard surface.

## 6. Proof Tricks Worth Reusing

- Package small-bids limit assumptions as explicit finite-instance families.
- Separate online-run feasibility, revenue accounting, dual feasibility, and
  explicit error terms before taking limits.
- For lower bounds, separate the hard distribution, payoff definition,
  harmonic cap, and randomized/Yao wrapper.

## 7. Library Lift Pass

Reusable finite AdWords infrastructure already lives in
`EconCSLib/Algorithms/Online/AdWords.lean`. The paper folder retains
source-route lemmas, Section 6/8 wrappers, and Theorem 9 lower-bound endpoints.
No additional lift is needed for this closeout.

## 8. DAG Audit

- Rendered artifact: `DependencyDAG.pdf` exists.
- Topology: the DAG covers the finite model, Balance rule, source-route
  Lemmas 1--7, Theorem 8, Section 6/8 extensions, and Theorem 9.
- Layout: the rendered artifact was previously checked for legible metadata,
  labels, and routing; this curation pass did not change the DAG source.

## 9. Conditional Results and Remaining Gaps

None. The paper-facing endpoints listed below are formalized.

## 10. Suspected Paper Errors or Inconsistencies

None found.

## 11. Validation Checks

- Dashboard review surface curated from 39 rows to 26 rows. Removed rows were
  broad proof-adapter variants, duplicate payoff aliases, or support endpoints
  already represented by final source-section statements.
- `python3 scripts/review_dashboard.py --paper MSVV07AdWords --statement-precheck`:
  36 rows; 36 Lean-to-TeX drafts; 36 statement-judge rows; no missing,
  stale, or flagged items.
- `python3 scripts/review_dashboard.py --paper MSVV07AdWords --assumption-precheck`:
  10 assumption declarations; no missing, stale, or flagged provenance rows.

## 12. Final Verdict

- Completion status: formalized.
- Summary: MSVV's paper-facing statement surface compiles, and the human review
  surface now contains 26 curated paper-facing rows rather than the previous
  39-row mixed surface. The approximation-accounting, state-invariant, and
  factor-revealing LP certificate APIs remain as internal proof infrastructure,
  not as unresolved paper-facing assumptions.

## 13. Paper Definitions Checked

These mathematical objects are exposed in `PaperInterface.lean` through
source-equation or source-condition wrapper rows.

- Multiple-slot distinctness: an advertiser appears at most once on one page.
  Lean: `paperSlotsPerPageDistinct_iff`.
- Spend and revenue accounting: advertiser spend and total assignment revenue.
  Lean: `paperSpend_formula`, `paperRevenue_formula`.
- Budget feasibility and small bids. Lean: `paperFeasible_iff`,
  `paperSmallBids_iff`.
- Fractional LP value and feasibility. Lean:
  `paperFractionalRevenue_formula`, `paperFractionalFeasible_iff`.
- Balance/MSVV discount, ratio, scaled bid, admissibility, and choice rule.
  Lean: `paperTradeoff_formula`, `paperMsvvRatio_formula`,
  `paperBalanceScore_formula`, `paperCanAssign_iff`,
  `paperIsBalanceChoice_iff`.
- Small-bids limiting family used by Theorem 8. Lean:
  `paperSmallBidsLimitFamily_fields`.
- Section 6 next-price charge definitions. Lean:
  `section6_next_highest_bid_all_formula`,
  `section6_next_highest_bid_alive_formula`.
- Theorem 9 hard distribution and capped normalized payoff. Lean:
  `theorem9HardDistribution_uniform`,
  `theorem9CappedNormalizedRevenue_formula`.

## 14. Named Theorem Statements Checked

### Theorem 8

**Paper statement.** Balance/MSVV is `1 - 1/e` competitive in the small-bids
limit.

**Lean interface statement.**
- `theorem8_balance_msvv_competitive_of_small_bids_limit_family`: paper-level
  limiting endpoint.

**Status.** formalized.

### Section 6 Extensions

**Paper statement.** The Balance/MSVV guarantee extends to different budgets,
nonexhaustive optima, effective/next-price charges, click-through rates,
delayed availability, and multiple slots.

**Lean interface statements.**
- `section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error`
- `section6_next_highest_bid_all_theorem8_finite_explicit_error`
- `section6_next_highest_bid_alive_theorem8_finite_explicit_error`
- `section6_click_through_rates_theorem8_finite_explicit_error`
- `section6_availability_theorem8_finite_explicit_error`
- `section6_page_top_balance_theorem8_finite_explicit_error`

**Status.** formalized.

### Section 8 Weighted Bids

**Paper statement.** The Balance/MSVV guarantee extends to advertiser-weighted
bids under the weighted effective-bid small-bids regime.

**Lean interface statement.**
- `section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids`

**Status.** formalized.

### Theorem 9

**Paper statement.** No randomized online algorithm beats the MSVV ratio on the
paper's hard distribution in the finite prefix model.

**Lean interface statement.**
- `theorem9_no_randomized_online_algorithm_beats_msvv_ratio`

**Status.** formalized.

### Source-Route Lemmas 1--7

**Paper statement.** The paper's factor-revealing and tradeoff-revealing LP
lemmas support the proof of Theorem 8.

**Lean audit statements.**
- Source-route wrappers live in `ProofInterface.lean` and
  `PostPaperAudit.lean`.

**Status.** formalized as audit endpoints; intentionally kept out of the
compact dashboard surface.

## 15. Paper-Facing Statement Validator Ledger

Generated from the curated dashboard surface. Human dashboard reviews and
model/agent statement checks may both appear here; this table records statement
target provenance and does not change the human-only review counter.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Balance score formula | `paperBalanceScore_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Query assignment admissibility | `paperCanAssign_iff` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Budget feasibility | `paperFeasible_iff` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Fractional LP feasibility | `paperFractionalFeasible_iff` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Fractional LP value | `paperFractionalRevenue_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Balance choice rule | `paperIsBalanceChoice_iff` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| MSVV ratio | `paperMsvvRatio_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Revenue formula | `paperRevenue_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Multiple-slot distinctness | `paperSlotsPerPageDistinct_iff` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Small-bids limiting family | `paperSmallBidsLimitFamily_fields` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Small-bids condition | `paperSmallBids_iff` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Spend formula | `paperSpend_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Balance tradeoff function | `paperTradeoff_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Section 6 availability | `section6_availability_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Section 6 click-through rates | `section6_click_through_rates_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Section 6 budgets/nonexhaustive optimum | `section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Section 6 alive next-highest-bid formula | `section6_next_highest_bid_alive_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Section 6 alive next-highest-bid guarantee | `section6_next_highest_bid_alive_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Section 6 all-bidders next-highest-bid formula | `section6_next_highest_bid_all_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Section 6 all-bidders next-highest-bid guarantee | `section6_next_highest_bid_all_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Section 6 page-level multiple slots | `section6_page_top_balance_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Section 8 weighted bids | `section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Theorem 8 limiting endpoint | `theorem8_balance_msvv_competitive_of_small_bids_limit_family` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
| Theorem 9 capped normalized payoff | `theorem9CappedNormalizedRevenue_formula` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Theorem 9 hard distribution | `theorem9HardDistribution_uniform` | gpt-5-codex (model; matches; 2026-06-11T03:14:55Z) | Source-equation wrapper matches the paper-facing statement. |
| Theorem 9 randomized-online lower bound | `theorem9_no_randomized_online_algorithm_beats_msvv_ratio` | gpt-5-codex (model; matches; 2026-06-07T00:00:39Z) | Paper and Lean statements match at comparable granularity. |
