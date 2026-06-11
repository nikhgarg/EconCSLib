# Competitive Auctions and Digital Goods

Machine-readable status source: [`status.json`](status.json).

## Source Version

- Formalization target: the SODA 2001 paper *Competitive Auctions and Digital
  Goods* by Andrew V. Goldberg, Jason D. Hartline, and Andrew Wright.
- Section 8.2 control source: the later journal version *Competitive Auctions*
  by Goldberg, Hartline, Karlin, Saks, and Wright, which refines Theorem 8.2
  to the monotone truthful randomized-auction formulation.
- Scope note: this folder formalizes the SODA paper. It is not a full inventory
  of all named results in the 2006 journal article.
- SODA listing: https://sigmod.org/publications/dblp/db/conf/soda/soda2001.html
- Public PDF mirror: https://www.cs.miami.edu/home/burt/learning/Csc597.052/docs/goldberg.pdf
- Journal PDF: https://users.eecs.northwestern.edu/~hartline/papers/auctions-journal.pdf

The source PDFs are public at the links above, but ignored local PDF and text
caches may be absent from a public checkout; regenerate a local text cache only
if needed for source searches. A 2026-06-01 web search did not find public
TeX/source.

## Central Theorem File

- `GHW01DigitalGoods/PaperInterface.lean` is the compact human-facing Lean
  surface with paper definitions and direct source theorem statements.
- `GHW01DigitalGoods/MainTheorems.lean`
- `GHW01DigitalGoods/PostPaperAudit.lean` is the importable source-numbered
  endpoint ledger.

Reusable auction definitions and theorem bodies live in
`EconCSLib/MechanismDesign/Auctions`.

## Current Status

This folder is formalized for the SODA paper. The reusable
auction primitives, benchmark support, and named SODA endpoints are formalized
under paper-facing source models. Theorem 8.2 uses the journal version's
refined monotone truthful randomized-auction wording; the preliminary
unrestricted wording is retained only as source-version audit material.

Theorem 6.2 constructs the ranked top-prefix sampling model internally,
Corollary 4.2 constructs the cutoff truncation internally, and Theorem 9.3 is
closed against the paper's set-of-bids focused-outcome convention.

## Maintenance Plan

1. Keep `PaperInterface.lean` as the compact human-facing surface. Public
   Section 8.2 and 9.3 endpoints should continue to consume source-shaped
   models, not raw proof adapters.
2. Keep the older anonymous sorted-bid, coupled-offer, and erased-bid-list
   adapter declarations available as auxiliary audit material only; do not
   promote them back into the paper-facing theorem signatures.
3. Keep the folder identity tied to the SODA paper. Mention the journal article
   only for the refined Theorem 8.2 monotone-auction wording unless journal-only
   results are added.
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
| Theorem 8.2, journal monotone truthful randomized auction revenue upper bound | `PaperInterface.theorem8_2_truthful_revenue_upper_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None. |
| Theorem 9.1, deterministic bid-independent lower bound | `PaperInterface.theorem9_1_bid_independent_lower_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; anonymous erased-bid-list binary model. |
| Lemma 9.2, truthful deterministic auctions are bid-independent | `PaperInterface.lemma9_2_threshold_domination` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; truthful deterministic IR/NPT binary auctions admit nonnegative threshold offers. |
| Theorem 9.3, deterministic truthful lower bound | `PaperInterface.theorem9_3_deterministic_truthful_lower_bound` | formalized | `GHW01DigitalGoods/PaperInterface.lean` | None; the public endpoint takes the paper's focused `A_i(B_i^x)` set-of-bids convention and constructs the erased-list/list-price representation internally. |

## Source-Audit Notes

The source audit records a Section 8.2 source-version distinction. The SODA
paper's Section 8.2 wording is broader than the later journal theorem, while
the journal version states and proves the revenue upper bound for monotone
truthful randomized auctions. This folder therefore uses the journal statement
for the Theorem 8.2 endpoint and keeps the preliminary wording only as
provenance/audit material.

This note does not reclassify the folder as a full formalization of the 2006
journal article; journal-only results are outside the current formalization
target.

## Maintainer Notes

- Last passing paper build: `lake build GHW01DigitalGoods`.
- Current status: formalized for the SODA paper. Section 8.2 follows the later
  journal version's refined monotone truthful randomized-offer theorem.
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
