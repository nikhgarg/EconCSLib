# GHW01 Formalization Plan

Last updated: 2026-05-31

## Current State

- `PaperInterface.lean` is the human-facing surface for the digital-goods
  auction statements.
- `MainTheorems.lean` contains proof-facing auction details and reusable
  support.
- `PostPaperAudit.lean` records additional validation checks.
- Current status is public partial, not fully formalized. The important
  remaining work is to derive the paper-model certificates currently assumed by
  Theorem 8.2 and Theorem 9.3.

## Review Plan

- Launch `review-dashboard.sh` and review each paper-facing theorem against the
  cached source.
- Prioritize theorem-numbered claims and benchmark definitions before auxiliary
  inequalities.
- Record any source mismatch in dashboard notes with the exact paper section or
  theorem number.

## Next Work

- Treat GHW01 as the next paper to try to finish completely.
- Derive `PaperTheorem82AnonymousSortedBidTruthfulModel` from primitive
  source-facing assumptions, or revise the theorem statement so any anonymity
  and adjacent-rank symmetry assumptions are explicit paper assumptions.
- Derive `PaperTheorem93AnonymousTruthfulDeterministicModel` from deterministic
  truthfulness plus Lemma 9.2, or revise the theorem statement so the
  anonymous erased-bid critical-price/list-price convention is explicit.
- Audit whether `PaperTheorem62FairCoinSortedModel` and
  `PaperCorollary42TruncationModel` can be constructed from the paper's stated
  fixed-price benchmark and truncation assumptions.
