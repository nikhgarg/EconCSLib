# Final Validation Report: MSVV07 AdWords

## 1. Human Verdict

- Lean formalization status: formalized
- Human dashboard review status: 0/39 rows reviewed; 0 stale; 0 mismatches.
- Human summary: This only uses a few lines of code as its infrastructure has largely been elevated to the shared auctions library.

- Lean formalization status: complete for the paper-facing endpoints exposed in
  `PaperInterface.lean`; no theorem-status endpoint is conditional.
- Human dashboard review status: `0/39` saved human review entries, `0` stale,
  `0` mismatch. This is an external review queue, not a Lean formalization gap.
- Paper correctness verdict: no suspected paper error found.
- Qualitative proof verdict: the main theorem endpoints are closed. Lean follows
  the paper's Balance/MSVV structure, but uses finite LP weak duality,
  explicit error bounds, and packaged limiting families to make the small-bids
  and lower-bound arguments precise.
- Lean footprint: `13228` root-inclusive MSVV Lean lines, including `13221`
  under `papers/MSVV07AdWords/`; `PaperInterface.lean` has `613` lines and
  exposes `39` review declarations.

## 2. Source and Scope

- Paper: *AdWords and Generalized Online Matching*.
- Source version: Journal of the ACM 54(5), 2007, Article 22, DOI
  `10.1145/1284320.1284321`; paper URL:
  `https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf`.
- Lean folder: `papers/MSVV07AdWords`.
- Human-facing statement surface: `papers/MSVV07AdWords/PaperInterface.lean`.
- Audit ledger: `papers/MSVV07AdWords/PostPaperAudit.lean`, imported by
  `papers/MSVV07AdWords.lean`.
- DAG artifacts: `papers/MSVV07AdWords/DependencyDAG.tex` and rendered
  `papers/MSVV07AdWords/DependencyDAG.pdf`.

## 3. What Has Been Proven

See the verdict and named-statement sections in this report.

## 4. Paper Definitions Checked

### Paper Interface

The paper definitions exposed for human review are the AdWords instance,
assignments, spend, revenue, budget feasibility, small-bids condition,
fractional LP value and feasibility, Balance/MSVV tradeoff function, competitive
ratio `1 - 1/e`, scaled Balance score, feasibility of assigning a query, and
the Balance choice rule.

Representative reader-facing Lean declarations:

- AdWords instance: `PaperInterface.PaperInstance`.
- Assignment and spend/revenue accounting: `PaperInterface.paperRevenue`.
- Budget feasibility: `PaperInterface.paperFeasible`.
- Small-bids condition: `PaperInterface.paperSmallBids`.
- Fractional LP benchmark: `PaperInterface.paperFractionalRevenue`.
- Balance/MSVV tradeoff function: `PaperInterface.paperTradeoff`.
- Balance choice rule: `PaperInterface.paperIsBalanceChoice`.
- Small-bids limiting family: `PaperInterface.PaperSmallBidsLimitFamily`.

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| abbrev PaperInstance | `PaperInstance` | uncertain. The draft exposes a Lean structure name but does not spell out the AdWords instance fields in paper language. |
| abbrev PaperAssignment | `PaperAssignment` | uncertain. The draft exposes a Lean structure name but does not spell out the assignment object in paper language. |
| abbrev paperSlotsPerPageDistinct | `paperSlotsPerPageDistinct` | uncertain. The draft is mostly a predicate signature and does not spell out the distinct-slot condition. |
| abbrev paperSpend | `paperSpend` | uncertain. The draft is mostly a function signature and does not state the spend formula. |
| abbrev paperRevenue | `paperRevenue` | uncertain. The draft is mostly a function signature and does not state the revenue formula. |
| abbrev paperFeasible | `paperFeasible` | uncertain. The draft is mostly a predicate signature and does not state the feasibility constraints. |
| abbrev paperSmallBids | `paperSmallBids` | uncertain. The draft is mostly a predicate signature and does not state the small-bids condition. |
| abbrev paperFractionalRevenue | `paperFractionalRevenue` | uncertain. The draft is mostly a function signature and does not state the fractional revenue formula. |
| abbrev PaperFractionalFeasible | `PaperFractionalFeasible` | uncertain. The draft exposes a Lean predicate name but does not spell out the fractional feasibility constraints. |
| abbrev paperTradeoff | `paperTradeoff` | uncertain. The draft is mostly a function signature and does not state the tradeoff expression. |
| abbrev paperMsvvRatio | `paperMsvvRatio` | uncertain. The draft is mostly a function signature and does not state the MSVV ratio expression. |
| abbrev paperBalanceScore | `paperBalanceScore` | uncertain. The draft is mostly a function signature and does not state the balance-score formula. |
| abbrev paperCanAssign | `paperCanAssign` | uncertain. The draft is mostly a predicate signature and does not state the admissibility condition. |
| abbrev paperIsBalanceChoice | `paperIsBalanceChoice` | uncertain. The draft is mostly a predicate signature and does not state the balance-choice rule. |
| abbrev PaperSmallBidsLimitFamily | `PaperSmallBidsLimitFamily` | uncertain. The draft exposes a Lean structure name but does not spell out the asymptotic small-bids family. |
| abbrev section6_next_highest_bid_all | `section6_next_highest_bid_all` | uncertain. The draft is mostly a function signature and does not state the next-highest-bid construction in paper language. |
| abbrev section6_next_highest_bid_alive | `section6_next_highest_bid_alive` | uncertain. The draft is mostly a function signature and does not state the alive-bid construction in paper language. |
| abbrev theorem9HardDistribution | `theorem9HardDistribution` | uncertain. The draft exposes a Lean structure name but does not spell out the hard distribution family. |
| abbrev theorem9IntegralPrefixAlgorithm | `theorem9IntegralPrefixAlgorithm` | uncertain. The draft exposes a Lean structure name but does not spell out the integral-prefix algorithm family. |
| abbrev theorem9RandomizedOnlineAlgorithm | `theorem9RandomizedOnlineAlgorithm` | uncertain. The draft exposes a Lean structure name but does not spell out the randomized online algorithm family. |
| abbrev theorem9FeasiblePrefixRuleFamily | `theorem9FeasiblePrefixRuleFamily` | uncertain. The draft exposes a Lean structure name but does not spell out the feasible prefix-rule family. |
| abbrev theorem9CappedNormalizedRevenue | `theorem9CappedNormalizedRevenue` | uncertain. The draft exposes a Lean structure name but does not spell out the capped normalized revenue expression. |
<!-- lean-derived-definitions:end -->

## 5. Named Theorem Statements Checked

### Named Results Checked

- Balance/MSVV algorithm definition: formalized through `paperBalanceScore`,
  `paperCanAssign`, and `paperIsBalanceChoice`.
- Lemmas 1--3: formalized as the source-route order, factor-revealing LP row,
  and geometric LP value/optimality statements used by the paper's equal-bids
  argument.
- Lemmas 4--7: formalized as the Section 5 LP optimality, right-hand-side
  perturbation, per-query tradeoff, and weighted perturbation/accounting
  statements used by the arbitrary-bids argument.
- Theorem 8: formalized in finite explicit-error form as
  `theorem8_finite_explicit_error`, and in limiting small-bids form as
  `theorem8_balance_msvv_competitive_of_small_bids_limit_family`.
- Section 6 extensions: formalized for different budgets, nonexhaustive optima,
  effective bids/next-price charges, click-through rates, delayed availability,
  slot expansion, the source-shaped page-level top-`n_q` distinct-bidder rule,
  and the distinct-choice invariant.
- Theorem 9: formalized for finite observed-prefix online algorithms, including
  the hard permutation distribution, capped normalized spend payoff, harmonic
  cap, and randomized lower-bound endpoints.
- Section 8 weighted bids: formalized by weighted effective-bid reductions and
  finite explicit-error Theorem 8 wrappers.

No named source theorem, lemma, proposition, or corollary identified in the
source audit is intentionally deferred or marked as not formalized.

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem8_finite_explicit_error | `theorem8_finite_explicit_error` | - Theorem 8, finite explicit-error form. For a complete finite query history, Balance/MSVV gets the `1 - 1/e` scaled offline optimum up to the explicit small-bids error. |
| theorem theorem8_balance_msvv_competitive_of_small_bids_limit_family | `theorem8_balance_msvv_competitive_of_small_bids_limit_family` | - Theorem 8, paper-level limiting endpoint. Any finite-query small-bids family satisfying the explicit threshold eventually has limiting competitive ratio `1 - 1/e`. |
| theorem section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error | `section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error` | - Section 6 items 1--2. Different advertiser budgets and nonexhaustive optima are already part of the base AdWords model, so the finite explicit Theorem 8 guarantee applies without changing the instance. |
| theorem section6_effective_bids_theorem8_finite_explicit_error | `section6_effective_bids_theorem8_finite_explicit_error` | - Section 6 effective-bid reduction: finite explicit Theorem 8 guarantee. |
| theorem section6_next_highest_bid_all_theorem8_finite_explicit_error | `section6_next_highest_bid_all_theorem8_finite_explicit_error` | - Section 6 next-highest-bid charges, all-bidders variant. |
| theorem section6_next_highest_bid_alive_theorem8_finite_explicit_error | `section6_next_highest_bid_alive_theorem8_finite_explicit_error` | - Section 6 next-highest-bid charges, alive-bidders variant. |
| theorem section6_click_through_rates_theorem8_finite_explicit_error | `section6_click_through_rates_theorem8_finite_explicit_error` | - Section 6 click-through rates: finite explicit Theorem 8 guarantee. |
| theorem section6_availability_theorem8_finite_explicit_error | `section6_availability_theorem8_finite_explicit_error` | - Section 6 delayed-entry availability: finite explicit Theorem 8 guarantee. |
| theorem section6_multiple_slots_theorem8_finite_explicit_error | `section6_multiple_slots_theorem8_finite_explicit_error` | - Section 6 multiple slots: finite explicit Theorem 8 guarantee. |
| theorem section6_page_top_balance_theorem8_finite_explicit_error | `section6_page_top_balance_theorem8_finite_explicit_error` | - Section 6 multiple slots: source-shaped page-level finite explicit Theorem 8 guarantee. On each page `q`, Balance chooses the top `slots q` distinct feasible advertisers by current scaled bid, and competes with the page-level offline o... |
| theorem section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct | `section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct` | - Section 6 multiple slots: the distinct-choice wrapper assigns any advertiser to at most one slot of each original query during the slot-expanded online run. |
| theorem section8_weighted_bids_theorem8_finite_explicit_error | `section8_weighted_bids_theorem8_finite_explicit_error` | - Section 8 advertiser weights: finite explicit Theorem 8 guarantee. |
| theorem section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids | `section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids` | - Section 8 advertiser weights, stated directly for the weighted effective-bid small-bids regime. |
| theorem theorem9_capped_normalized_revenue_eq_prefix_spend | `theorem9_capped_normalized_revenue_eq_prefix_spend` | - The canonical payoff for integral prefix algorithms is definitionally the paper's capped normalized spend. |
| theorem theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio | `theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio` | - Theorem 9, broad observed-prefix lower-bound endpoint. No randomized distribution over any finite family of feasible observed-prefix allocation rules can beat the MSVV ratio on every sufficiently large hard instance. |
| theorem theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio | `theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio` | - Theorem 9, lower-bound endpoint for randomized distributions over deterministic integral prefix algorithms. |
| theorem theorem9_no_randomized_online_algorithm_beats_msvv_ratio | `theorem9_no_randomized_online_algorithm_beats_msvv_ratio` | - Theorem 9, paper-facing randomized online algorithm endpoint in the finite prefix model. |
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper MSVV07AdWords --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| abbrev PaperAssignment | `PaperAssignment` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the assignment object in paper language. |
| abbrev PaperFractionalFeasible | `PaperFractionalFeasible` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean predicate name but does not spell out the fractional feasibility constraints. |
| abbrev PaperInstance | `PaperInstance` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the AdWords instance fields in paper language. |
| abbrev PaperSmallBidsLimitFamily | `PaperSmallBidsLimitFamily` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the asymptotic small-bids family. |
| abbrev paperBalanceScore | `paperBalanceScore` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the balance-score formula. |
| abbrev paperCanAssign | `paperCanAssign` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a predicate signature and does not state the admissibility condition. |
| abbrev paperFeasible | `paperFeasible` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a predicate signature and does not state the feasibility constraints. |
| abbrev paperFractionalRevenue | `paperFractionalRevenue` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the fractional revenue formula. |
| abbrev paperIsBalanceChoice | `paperIsBalanceChoice` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a predicate signature and does not state the balance-choice rule. |
| abbrev paperMsvvRatio | `paperMsvvRatio` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the MSVV ratio expression. |
| abbrev paperRevenue | `paperRevenue` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the revenue formula. |
| abbrev paperSlotsPerPageDistinct | `paperSlotsPerPageDistinct` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a predicate signature and does not spell out the distinct-slot condition. |
| abbrev paperSmallBids | `paperSmallBids` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a predicate signature and does not state the small-bids condition. |
| abbrev paperSpend | `paperSpend` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the spend formula. |
| abbrev paperTradeoff | `paperTradeoff` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the tradeoff expression. |
| theorem section6_availability_theorem8_finite_explicit_error | `section6_availability_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section6_click_through_rates_theorem8_finite_explicit_error | `section6_click_through_rates_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error | `section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section6_effective_bids_theorem8_finite_explicit_error | `section6_effective_bids_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct | `section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section6_multiple_slots_theorem8_finite_explicit_error | `section6_multiple_slots_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev section6_next_highest_bid_alive | `section6_next_highest_bid_alive` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the alive-bid construction in paper language. |
| theorem section6_next_highest_bid_alive_theorem8_finite_explicit_error | `section6_next_highest_bid_alive_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev section6_next_highest_bid_all | `section6_next_highest_bid_all` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft is mostly a function signature and does not state the next-highest-bid construction in paper language. |
| theorem section6_next_highest_bid_all_theorem8_finite_explicit_error | `section6_next_highest_bid_all_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section6_page_top_balance_theorem8_finite_explicit_error | `section6_page_top_balance_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section8_weighted_bids_theorem8_finite_explicit_error | `section8_weighted_bids_theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids | `section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem8_balance_msvv_competitive_of_small_bids_limit_family | `theorem8_balance_msvv_competitive_of_small_bids_limit_family` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem8_finite_explicit_error | `theorem8_finite_explicit_error` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem9CappedNormalizedRevenue | `theorem9CappedNormalizedRevenue` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the capped normalized revenue expression. |
| abbrev theorem9FeasiblePrefixRuleFamily | `theorem9FeasiblePrefixRuleFamily` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the feasible prefix-rule family. |
| abbrev theorem9HardDistribution | `theorem9HardDistribution` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the hard distribution family. |
| abbrev theorem9IntegralPrefixAlgorithm | `theorem9IntegralPrefixAlgorithm` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the integral-prefix algorithm family. |
| abbrev theorem9RandomizedOnlineAlgorithm | `theorem9RandomizedOnlineAlgorithm` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:51Z): The draft exposes a Lean structure name but does not spell out the randomized online algorithm family. |
| theorem theorem9_capped_normalized_revenue_eq_prefix_spend | `theorem9_capped_normalized_revenue_eq_prefix_spend` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio | `theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio | `theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem9_no_randomized_online_algorithm_beats_msvv_ratio | `theorem9_no_randomized_online_algorithm_beats_msvv_ratio` | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:51Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Additional Assumptions Beyond Paper

None separately recorded in the existing report.

## 8. Proof-Strategy Deviations

### Modeling and Proof Notes

- Theorem 8 is proved through concrete finite Balance history accounting and a
  small-bids limiting wrapper. The source-route Lemmas 1--7 are also exposed in
  the audit ledger, so the paper proof structure remains inspectable without
  making those helper statements the final theorem endpoint.
- Section 6 multiple slots are represented by a page-level model that selects
  the top `n_q` distinct feasible bidders for each arriving page and compares
  against a page-level offline optimum with the same budget and cardinality
  constraints.
- Theorem 9 uses a finite observed-prefix algorithm model. The paper-facing
  randomized online endpoint is a specialization of a broader feasible-prefix
  lower-bound theorem.
- No additional assumption is hidden in prose. Side conditions that matter in
  Lean, such as nonnegative bids, positive budgets, finite query histories,
  distinct histories, and small-bids thresholds, appear in the theorem
  statements.

## 9. Proof Tricks Worth Reusing

### Reusable Lessons

- Keep the human statement surface compact and paper-shaped; keep exhaustive
  helper inventories in `PostPaperAudit.lean`.
- Package small-bids limit assumptions as explicit finite-instance families.
- Separate online-run feasibility, revenue accounting, dual feasibility, and
  explicit error terms before taking limits.
- For lower bounds, separate the hard distribution, deterministic algorithm
  model, payoff definition, harmonic cap, and randomized/Yao wrapper.

## 10. Library Lift Pass

None separately recorded in the existing report.

## 11. DAG Audit

### External Review and DAG

- The dashboard has `39` rows: `22` paper definitions/formula objects and `17`
  theorem endpoints. This is a conservative full paper-interface audit surface;
  the headline theorem-only subset would be smaller.
- The DAG was rendered with `latexmk` on 2026-05-25. The rendered PDF was
  converted to an image and visually inspected: metadata, legend, nodes, labels,
  and arrows are legible, with no observed text overlap or missing paper-facing
  boxes.

## 12. Conditional Results and Remaining Gaps

None separately recorded in the existing report.

## 13. Suspected Paper Errors or Inconsistencies

None separately recorded in the existing report.

## 14. Validation Checks

### Verification Checks

- `lake build MSVV07AdWords`: passed on 2026-05-25.
- Full `lake build`: passed on 2026-05-25.
- `python3 scripts/check_smoke.py --include-papers`: passed on 2026-05-25,
  including the MSVV root and all non-active paper roots.
- Dashboard cache/precheck: cache refreshed on 2026-05-25; precheck reports
  `0/39` human review entries, `0` stale rows, and `0` mismatches. The strict
  dashboard check exits nonzero only because the 39 optional human-review
  entries have not been saved.
- MSVV-filtered repository audit: passed on 2026-05-25 with no MSVV-specific
  findings.
- Full repository audit: rerun on 2026-05-25. It still reports unrelated
  non-MSVV issues: missing cached source PDFs, absent dashboard caches or large
  dashboard slices for other papers, and status-vocabulary issues in other
  paper READMEs.
- Placeholder audit over MSVV Lean files: no `sorry`, `admit`, or `axiom` in
  the claimed MSVV paper files.
- DAG render: paper-local `latexmk` succeeded and produced
  `DependencyDAG.pdf`; the full `scripts/compile_dependency_dags.sh` pass also
  succeeded after cleaning stale `latexmk` state and making the MiKTeX package
  tree visible to TeX.
- `git diff --check`: passed on 2026-05-25.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 39 rows; 17 match, 22 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: passes (39 rows; digest 475d4a714491).

Flagged rows:
- `PaperInstance`: uncertain. The draft exposes a Lean structure name but does not spell out the AdWords instance fields in paper language.
- `PaperAssignment`: uncertain. The draft exposes a Lean structure name but does not spell out the assignment object in paper language.
- `paperSlotsPerPageDistinct`: uncertain. The draft is mostly a predicate signature and does not spell out the distinct-slot condition.
- `paperSpend`: uncertain. The draft is mostly a function signature and does not state the spend formula.
- `paperRevenue`: uncertain. The draft is mostly a function signature and does not state the revenue formula.
- `paperFeasible`: uncertain. The draft is mostly a predicate signature and does not state the feasibility constraints.
- `paperSmallBids`: uncertain. The draft is mostly a predicate signature and does not state the small-bids condition.
- `paperFractionalRevenue`: uncertain. The draft is mostly a function signature and does not state the fractional revenue formula.
- `PaperFractionalFeasible`: uncertain. The draft exposes a Lean predicate name but does not spell out the fractional feasibility constraints.
- `paperTradeoff`: uncertain. The draft is mostly a function signature and does not state the tradeoff expression.
- `paperMsvvRatio`: uncertain. The draft is mostly a function signature and does not state the MSVV ratio expression.
- `paperBalanceScore`: uncertain. The draft is mostly a function signature and does not state the balance-score formula.
- `paperCanAssign`: uncertain. The draft is mostly a predicate signature and does not state the admissibility condition.
- `paperIsBalanceChoice`: uncertain. The draft is mostly a predicate signature and does not state the balance-choice rule.
- `PaperSmallBidsLimitFamily`: uncertain. The draft exposes a Lean structure name but does not spell out the asymptotic small-bids family.
- `section6_next_highest_bid_all`: uncertain. The draft is mostly a function signature and does not state the next-highest-bid construction in paper language.
- `section6_next_highest_bid_alive`: uncertain. The draft is mostly a function signature and does not state the alive-bid construction in paper language.
- `theorem9HardDistribution`: uncertain. The draft exposes a Lean structure name but does not spell out the hard distribution family.
- `theorem9IntegralPrefixAlgorithm`: uncertain. The draft exposes a Lean structure name but does not spell out the integral-prefix algorithm family.
- `theorem9RandomizedOnlineAlgorithm`: uncertain. The draft exposes a Lean structure name but does not spell out the randomized online algorithm family.
- `theorem9FeasiblePrefixRuleFamily`: uncertain. The draft exposes a Lean structure name but does not spell out the feasible prefix-rule family.
- `theorem9CappedNormalizedRevenue`: uncertain. The draft exposes a Lean structure name but does not spell out the capped normalized revenue expression.

## 15. Final Verdict

The MSVV AdWords paper-facing Lean endpoints are complete and non-conditional.
The remaining dashboard work is human review of the exposed declarations, not a
missing formal proof. The DAG now renders locally and has been visually checked.

- Completion status: formalized.
- Summary: This only uses a few lines of code as its infrastructure has largely been elevated to the shared auctions library.
