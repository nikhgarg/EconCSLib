# Competitive Auctions and Digital Goods

## Source Version

- Primary formalized source: the later journal version *Competitive Auctions*
  by Andrew V. Goldberg, Jason D. Hartline, Anna R. Karlin, Michael Saks, and
  Andrew Wright.
- Historical source and numbering crosswalk: *Competitive Auctions and Digital
  Goods* by Andrew V. Goldberg, Jason D. Hartline, and Andrew Wright, public
  InterTrust technical report STAR-TR-99-01, revised November 2000; folder name
  and source-numbered audit aliases follow the SODA 2001 citation.
- SODA listing: https://sigmod.org/publications/dblp/db/conf/soda/soda2001.html
- Public PDF mirror: https://www.cs.miami.edu/home/burt/learning/Csc597.052/docs/goldberg.pdf
- Journal PDF: https://users.eecs.northwestern.edu/~hartline/papers/auctions-journal.pdf

The extracted text cache `GHW01DigitalGoods.txt` is tracked and used for
named-statement searches. The source PDFs are public at the links above, but
the ignored local PDF cache may be absent from a public checkout; refresh the
text cache only if the source PDF changes. A 2026-06-01 web search did not find
public TeX/source. The later journal version is the controlling source where it
refines the preliminary text: it clarifies anonymity/set-of-bids and
masked-vector language, and it supplies the corrected Section 8.2
monotone-auction statement. This folder keeps the InterTrust/SODA
theorem-number labels as a crosswalk for the existing Lean audit endpoints;
where the preliminary and journal statements conflict, the journal statement
controls.

## Central Theorem File

- `GHW01DigitalGoods/PaperInterface.lean` is the compact human-facing Lean
  surface with paper definitions and direct source theorem statements.
- `GHW01DigitalGoods/MainTheorems.lean`
- `GHW01DigitalGoods/PostPaperAudit.lean` is the importable source-numbered
  endpoint ledger.

Reusable auction definitions and theorem bodies live in
`EconCSLib/MechanismDesign/Auctions`.

## Current Status

This folder is formalized. The reusable auction primitives, benchmark support,
and named theorem endpoints are formalized under paper-facing source models,
and the Theorem 8.2, Theorem 9.3, Theorem 6.2, and Corollary 4.2 public
wrappers no longer take the old raw proof-adapter structures directly.
Theorem 6.2 constructs the ranked top-prefix sampling model internally,
Corollary 4.2 constructs the cutoff truncation internally, Theorem 9.3 is
closed against the paper's set-of-bids focused-outcome convention, and Theorem
8.2 is closed against the journal version's monotone truthful
randomized-offer theorem. The literal weak-DSIC/bid-independent reading of the
technical-report Theorem 8.2 is kept as a source-audit counterexample: a
two-bidder threshold auction can earn `101` against fixed-price benchmark
`100` on bids `{1, 100}`.

## Maintenance Plan

1. Keep `PaperInterface.lean` as the compact human-facing surface. Public
   Section 8.2 and 9.3 endpoints should continue to consume source-shaped
   models, not raw proof adapters.
2. Keep the older anonymous sorted-bid, coupled-offer, and erased-bid-list
   adapter declarations available as auxiliary audit material only; do not
   promote them back into the paper-facing theorem signatures.
3. If maintainers retitle this folder around the journal version, update the
   source identity, theorem-number crosswalk, README, final report, DAG, and
   root status rows together.
4. Consider extracting the finite PMF layer-cake surplus lemmas behind
   Theorem 8.2 into reusable stochastic-ordering infrastructure when a second
   paper needs them.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Digital-goods auction interface, revenue, DSIC | `PaperInterface.revenue`, `PaperInterface.truthful` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; finite bidder digital-goods model. |
| Posted-price and threshold-auction truthfulness/IR/NPT | `paper_posted_price_truthful`, `paper_threshold_price_truthful`, `paper_own_erased_threshold_price_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; threshold prices must be own-bid independent, and NPT uses nonnegative prices. |
| Fixed-price benchmark and two-winner benchmark | `PaperInterface.singlePriceRevenue`, `PaperInterface.fixedPriceBenchmark`, `PaperInterface.twoWinnerBenchmark` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None. |
| Theorem 4.1, high-value fixed-price lower bound | `PaperInterface.theorem4_1_high_value` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; base-two real-log wrapper with `Real.logb 2 h + 2`. |
| Corollary 4.2, cutoff truncation fixed-price lower bound | `PaperInterface.corollary4_2_fixed_price_lower_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; the `h / n` cutoff truncation and scaled benchmark comparison are constructed internally. |
| Lemma 6.1, random subset revenue split | `PaperInterface.lemma6_1_fair_coin` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; independent fair-coin lower-tail form. |
| Theorem 6.2, random sampling auction guarantee | `PaperInterface.theorem6_2_random_sampling` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; the ranked top-prefix sampling model is constructed internally from the finite candidate benchmark and `alpha * h <= F`. |
| Theorem 7.1, weighted pairing auction revenue | `PaperInterface.theorem7_1_weighted_pairing` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; normalized bids in `[1,h]`, source condition `4h <= T`, and rounded `log_2 h + 2` coefficient. |
| Theorem 7.2, weighted auction benchmark bound | `PaperInterface.theorem7_2_weighted_pairing_benchmark` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; includes the `F^(2) <= 576 * s * W` bound under the paper's large-benchmark/log side conditions. |
| Lemma 8.1, monotone win probabilities in truthful auctions | `PaperInterface.lemma8_1_truthful_monotone` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None. |
| Theorem 8.2, journal monotone truthful randomized auction revenue upper bound | `PaperInterface.theorem8_2_truthful_revenue_upper_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; the endpoint uses the journal raw marginal-offer CDF monotonicity model and derives the ranked surplus recursion directly. The weak InterTrust/SODA reading is refuted by `PaperInterface.theorem8_2_weak_truthful_counterexample`. |
| Theorem 9.1, deterministic bid-independent lower bound | `PaperInterface.theorem9_1_bid_independent_lower_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; anonymous erased-bid-list binary model. |
| Lemma 9.2, truthful deterministic auctions are bid-independent | `PaperInterface.lemma9_2_threshold_domination` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; truthful deterministic IR/NPT binary auctions admit nonnegative threshold offers. |
| Theorem 9.3, deterministic truthful lower bound | `PaperInterface.theorem9_3_deterministic_truthful_lower_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; the public endpoint takes the paper's focused `A_i(B_i^x)` set-of-bids convention and constructs the erased-list/list-price representation internally. |

## Source-Audit Notes

The cached text contains Theorem 4.1, Corollary 4.2, Lemma 6.1, Theorem 6.2,
Theorems 7.1--7.2, Lemma 8.1, Theorem 8.2, Theorem 9.1, Lemma 9.2, and Theorem
9.3. Current Lean coverage includes the reusable digital-goods mechanism layer,
fixed-price benchmark support, deterministic RSOP-style truthfulness skeleton,
Section 6 deterministic/probabilistic independent-sampling bridges with the
paper's top-prefix exponential constants, the Section 7 concrete factor-two
ranked-bin weighted-pairing bridge, the closed Theorem 4.1 natural-number
dyadic and `Real.logb 2 h + 2` forms, paper-condition `Real.logb` wrappers for
Theorems 7.1--7.2, the closed Theorem 7.2 natural-number dyadic lower-bound and
repeated-bid tightness-family endpoints, Corollary 4.2's cutoff truncation,
Lemma 8.1, and Lemma 9.2. Theorem 8.2 is formalized using the journal
version's monotone truthful randomized-auction statement, with the broad
technical-report wording recorded as a refuted weak reading. Theorem 9.3 is
closed against the paper's set-of-bids focused-outcome deterministic auction
convention.

## Maintainer Notes

- Last passing paper build: `lake build GHW01DigitalGoods`.
- Current status: formalized. The old broad technical-report Theorem 8.2
  wording is false; the journal monotone randomized-offer endpoint is the
  controlling paper-facing theorem used here.
- Do not redo: Section 7.2 tightness for `ghwTightValue`; it is closed through
  `paper_theorem7_2_tightness_ratio_for_repeated_bid_family`.
- Do not redo: Theorem 4.1 now has a verified base-two real-log wrapper,
  `paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value`.
- Do not redo: Theorem 6.2 is closed by
  `paper_theorem6_2_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha`;
  it constructs the ranked top-prefix model internally and keeps
  `alpha * h <= F` as the source theorem assumption.
- Do not redo: Corollary 4.2 is closed by
  `paper_corollary4_2_fixed_price_lower_bound_of_card_truncation`, which
  constructs the `h / n` cutoff truncation and scaled benchmark comparison
  internally.
- Current best Section 8 endpoint:
  `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_offer_source_model`.
  It formalizes the journal raw CDF marginal-offer condition directly:
  adjacent CDF inequalities imply monotone ranked acceptance probabilities and
  the adjacent surplus recursion by finite PMF layer-cake algebra. The older
  coupled-offer endpoint remains in the reusable library only as support/audit
  material for the journal proof sketch and is no longer a public paper
  assumption.
- Current best Section 9.3 endpoint:
  `paper_theorem9_3_deterministic_truthful_ratio_witness_of_primitive_set_of_bids_source_model`.
  It takes the deterministic truthful auction family plus the paper's
  focused `A_i(B_i^x)` set-of-bids convention, derives global erased-list
  relabeling and the specialized erased-bid offer anonymity bridge, then uses
  Lemma 9.2 to select representative erased-list critical prices internally.
  Primitive price-rule endpoints remain in the reusable auction library as
  bid-independent specializations, not as the GHW paper-facing theorem.
