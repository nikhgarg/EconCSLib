# Final Validation Report: Competitive Auctions and Digital Goods

## 1. Human Verdict

- Lean formalization status: formalized.
- Human dashboard review status: 0/18 rows reviewed; 0 stale; 0 mismatches.
- LLM statement-translation audit: 18/18 rows match.
- Human summary: Formalizes the SODA paper; Theorem 8.2 uses the
  refined monotone-auction wording from the journal version.
- Paper correctness verdict: no inconsistency is reported for the formalized
  target. The source-version note is that preliminary Section 8.2 wording is
  broader than the later journal theorem; this folder uses the journal
  monotone-auction statement for Theorem 8.2.
- Qualitative proof verdict: the formalization follows the SODA paper's section
  structure, with Theorem 8.2 checked against the journal refinement.

## 2. Source and Scope

- Primary formalization target: *Competitive Auctions and Digital Goods* by
  Andrew V. Goldberg, Jason D. Hartline, and Andrew Wright, the SODA 2001
  digital-goods paper.
- Section 8.2 control source: the later journal version *Competitive Auctions*
  by Andrew V. Goldberg, Jason D. Hartline, Anna R. Karlin, Michael Saks, and
  Andrew Wright. For Theorem 8.2, Lean formalizes the journal version's
  monotone truthful randomized-auction revenue upper bound.
- Scope note: this report is not a full inventory of all named results in the
  2006 journal article. Journal-only results are outside the current
  formalization target.
- Human-facing Lean file: `PaperInterface.lean`.
- Importable audit ledger: `PostPaperAudit.lean`.
- DAG artifacts: `DependencyDAG.tex` and regenerated `DependencyDAG.pdf`.

## 3. What Has Been Proven

The paper's digital-goods mechanism definitions, truthful threshold mechanisms,
fixed-price benchmarks, random-sampling bounds, weighted-pairing bounds,
Section 8.2 monotone randomized-auction revenue upper bound, deterministic
bid-independent lower bound, deterministic truthfulness threshold structure,
and deterministic truthful lower bound are all represented by compiling
paper-facing endpoints.

Corollary 4.2 and Theorem 6.2 no longer take external model witnesses:
truncation and ranked top-prefix sampling are constructed internally. Theorem
8.2 uses the later journal monotone-auction formulation as the Section 8.2
endpoint. Theorem 9.3 no longer takes an anonymous erased-bid/list-price
representation as a public assumption; it is derived from the source-shaped
deterministic auction model.

## 4. Paper Definitions Checked

- Digital-goods revenue: total payments collected from all bidders. Lean:
  `PaperInterface.revenue`.
- Dominant-strategy truthfulness: truthful reporting weakly dominates any
  single-agent report deviation. Lean: `PaperInterface.truthful`.
- Single-price revenue and fixed-price benchmark. Lean:
  `PaperInterface.singlePriceRevenue`, `PaperInterface.fixedPriceBenchmark`.
- Two-winner fixed-price benchmark `F^(2)`. Lean:
  `PaperInterface.twoWinnerBenchmark`.
- Total bid value `T`. Lean: `PaperInterface.totalValue`.
- Weighted-pairing expected revenue. Lean:
  `PaperInterface.weightedPairingRevenue`.

## 5. Named Theorem Statements Checked

- Theorem 4.1: high-value profiles satisfy the logarithmic fixed-price lower
  bound. Lean: `theorem4_1_high_value`. Status: formalized.
- Corollary 4.2: cutoff truncation gives the factor-four fixed-price lower
  bound. Lean: `corollary4_2_fixed_price_lower_bound`. Status: formalized.
- Lemma 6.1: fair-coin lower-tail estimate. Lean: `lemma6_1_fair_coin`.
  Status: formalized.
- Theorem 6.2: random sampling auction revenue guarantee. Lean:
  `theorem6_2_random_sampling`. Status: formalized.
- Theorem 7.1: weighted pairing gets the logarithmic guarantee under
  `4h <= T`. Lean: `theorem7_1_weighted_pairing`. Status: formalized.
- Theorem 7.2: weighted pairing competes with `F^(2)` under `F^(2) >= 2h`.
  Lean: `theorem7_2_weighted_pairing_benchmark`. Status: formalized.
- Lemma 8.1: truthfulness implies monotone win probabilities. Lean:
  `lemma8_1_truthful_monotone`. Status: formalized.
- Theorem 8.2, Section 8 source-version endpoint: monotone truthful randomized
  auctions have expected revenue at most `F`. Lean:
  `theorem8_2_truthful_revenue_upper_bound`. Status: formalized for the later
  journal statement used as the Section 8.2 endpoint.
- Theorem 9.1: bid-independent auctions have a lower-bound witness. Lean:
  `theorem9_1_bid_independent_lower_bound`. Status: formalized.
- Lemma 9.2: truthful deterministic binary auctions admit threshold offers.
  Lean: `lemma9_2_threshold_domination`. Status: formalized.
- Theorem 9.3: deterministic truthful auctions have the lower-bound witness.
  Lean: `theorem9_3_deterministic_truthful_lower_bound`. Status: formalized.

## 6. Paper-Facing Statement Validator Ledger

The paper-facing review surface contains 18 rows: 7 definitions and 11 theorem,
lemma, or corollary endpoints. The Section 8.2 source-version audit endpoint is
kept in `PostPaperAudit.lean` and is not part of this paper-facing inventory.

Summary: 18 rows; 18 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar
rows: none after removing the non-paper-facing audit row from the sidecars.

## 7. Additional Assumptions Beyond Paper

None. The paper-facing source models package the paper's own conventions:
finite bidder profiles, nonnegative values/prices where the auction model
requires them, journal raw-CDF monotonicity for Section 8.2, and anonymous
set-of-bids/masked-vector behavior for Section 9.3.

## 8. Proof-Strategy Deviations

- Section 8.2 is checked against the later journal monotone-auction statement.
  Lean proves a finite raw-CDF/PMF version of the journal argument.
- Section 9.3 derives the erased-list/list-price bridge internally from the
  paper's set-of-bids convention and Lemma 9.2.

## 9. Proof Tricks Worth Reusing

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

`DependencyDAG.tex` identifies the SODA paper as the target and notes that
Section 8.2 uses the journal refinement. The DAG uses closed dependency arrows
only; there are no open or conditional DAG nodes.

## 12. Conditional Results and Remaining Gaps

None under the source-version choice recorded above. Theorem 8.2 is the journal
raw-CDF monotone-offer theorem. Theorem 9.3 is the deterministic truthful
theorem under the paper's set-of-bids focused-outcome convention. All
bridge/adaptation work from those source-shaped models is discharged
internally. Older coupled-offer and proof-adapter declarations remain only as
auxiliary reusable-library/audit material.

## 13. Suspected Paper Errors or Inconsistencies

No paper error is reported for the formalized target. The only recorded issue
is a source-version distinction in Section 8.2; it is documented under
Source-Version Notes.

## Source-Version Notes

Section 8.2 is a source-version distinction: the SODA paper's wording is
broader than the later journal theorem, while the journal version states and
proves the revenue upper bound for monotone truthful randomized auctions. This
folder therefore uses the journal statement for the Section 8.2 endpoint and
retains the preliminary wording only as provenance/audit material.

## 14. Validation Checks

- `lake build GHW01DigitalGoods`: passed in the private and public checkouts.
- `python3 scripts/sync_paper_status.py`: passed in the private and public
  checkouts.
- `bash scripts/compile_dependency_dags.sh`: passed in the private and public
  checkouts.
- `python3 scripts/audit_repository.py`: passed with 0 errors in the private
  and public checkouts. Remaining warnings are repository hygiene warnings
  about omitted source-PDF caches, missing dashboard caches, top-level README
  length, and existing non-GHW README wording.
- `python3 scripts/generate_paper_status_table.py`: passed in the workshop
  paper folder.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error
  garg_econcslib_2026.tex`: passed in the workshop paper folder.

## 15. Final Verdict

Completion status: formalized.

Summary: The folder formalizes the SODA paper. Theorem 8.2 uses
the refined monotone-auction wording from the journal version. This is not a
full inventory of all named results in the 2006 journal article.
