# Final Validation Report: Competitive Auctions and Digital Goods

## Verdict

Verified under the paper-facing Lean models in `GHW01DigitalGoods`.

The paper's named main results are represented by direct statement endpoints in
`PaperInterface.lean`, with source-numbered audit aliases in
`PostPaperAudit.lean` and status/dependency summaries in `README.md` and
`DependencyDAG.tex`.

## Source checked

- Paper: *Competitive Auctions and Digital Goods*
- Authors: Andrew V. Goldberg, Jason D. Hartline, and Andrew Wright
- Local source: `GHW01DigitalGoods.pdf`
- Local text cache: `GHW01DigitalGoods.txt`
- Version note: public InterTrust technical report STAR-TR-99-01, revised
  November 2000; folder name follows the SODA 2001 citation.

## Named-result inventory

| Source result | Text-cache line | Audit declaration |
|---|---:|---|
| Theorem 4.1 | 359 | `audit_theorem4_1_high_value` |
| Corollary 4.2 | 301 | `audit_corollary4_2_truncation` |
| Lemma 6.1 | 428 | `audit_lemma6_1_fair_coin` |
| Theorem 6.2 | 479 | `audit_theorem6_2_random_sampling` |
| Theorem 7.1 | 563 | `audit_theorem7_1_weighted_pairing` |
| Theorem 7.2 | 626 | `audit_theorem7_2_weighted_pairing_benchmark` |
| Lemma 8.1 | 747 | `audit_lemma8_1_truthful_monotone` |
| Theorem 8.2 | 833 | `audit_theorem8_2_truthful_revenue_upper_bound` |
| Theorem 9.1 | 979 | `audit_theorem9_1_bid_independent_lower_bound` |
| Lemma 9.2 | 1105 | `audit_lemma9_2_threshold_domination` |
| Theorem 9.3 | 1100 | `audit_theorem9_3_deterministic_truthful_lower_bound` |

## Cross-artifact checks

- Paper text: the cached text contains every named theorem/lemma/corollary
  claimed in the README source-audit notes.
- README: each named result has a status row using the controlled vocabulary
  from `docs/STATUS.md`; no named source result remains `conditional`,
  `partially formalized`, `scaffold`, or `not started`.
- DAG: every source theorem/lemma node is either `dag_result` for closed
  paper-facing results or `dag_model` for model/definition layers. The remaining
  dashed arrows are paper-route/context links, not unresolved assumptions.
- Paper-facing Lean: `PaperInterface.lean` is the human-facing statement
  surface. `PostPaperAudit.lean` restates one source-numbered audit theorem per
  final endpoint and proves each by a thin call to the exported paper-facing
  theorem.

## Deliberate model conventions

- Logarithms are represented with base-two real logs plus the explicit finite
  dyadic rounding term `+ 2`, e.g. `Real.logb 2 h + 2`.
- Lemma 6.1 and Theorem 6.2 are formalized in the independent fair-coin
  sampling model used by the Lean random-sampling development.
- Theorem 8.2 uses an explicit anonymous sorted-bid certificate that packages
  the paper's ranked-bid convention and adjacent-rank symmetry assumptions.
- Theorem 9.1 is stated in the paper's anonymous erased-bid-list binary model.
- Theorem 9.3 packages anonymous truthful deterministic binary auctions with
  IR, no positive transfers, binary allocation, and the erased-bid critical
  price convention.

## Verification checks

- The paper root module imports `PaperInterface.lean`, `MainTheorems.lean`, and
  `PostPaperAudit.lean`.
- The paper Lean target builds successfully.
- The dependency DAG renders successfully after the audit updates.
