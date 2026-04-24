# Competitive Auctions and Digital Goods

## Source Version

- Paper: *Competitive Auctions and Digital Goods*
- Authors: Andrew V. Goldberg, Jason D. Hartline, and Andrew Wright
- Version formalized: SODA 2001 / 2021 SIGecom Test of Time Award paper
- Award page: https://ec21.sigecom.org/program/awards/index.html
- ACM SIGecom Test-of-Time listing: https://www.sigecom.org/award-tot.html
- Public PDF mirror: https://kylewoodward.com/blog-data/pdfs/references/goldberg%2Bhartline%2Bwright--2001A.pdf
- Accessed: 2026-04-23

The PDF is not committed to git. Use the SODA 2001 paper linked above as the
source version for the currently scaffolded digital-goods track.

## Central Theorem File

- `EconCSLean/Auction/MainTheorems.lean`

That file contains the paper-facing theorem wrappers currently available. The
full competitive-auction benchmark theorem is not yet formalized.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Unlimited-supply digital-goods auction interface | `DigitalGoodsAuction` | formalized | `EconCSLean/Auction/DigitalGoods.lean` | none |
| Quasilinear utility | `DigitalGoodsAuction.utility` | formalized | `EconCSLean/Auction/DigitalGoods.lean` | none |
| Posted-price truthfulness | `paper_posted_price_truthful` | formalized | `EconCSLean/Auction/MainTheorems.lean` | none |
| Posted-price individual rationality | `paper_posted_price_individually_rational` | formalized | `EconCSLean/Auction/MainTheorems.lean` | none |
| Posted-price no-positive-transfers theorem | `paper_posted_price_no_positive_transfers` | formalized | `EconCSLean/Auction/MainTheorems.lean` | nonnegative prices |
| Competitive revenue benchmark | none | not started | none | define fixed-price benchmark and revenue |
| Random-sampling competitive auction guarantee | none | not started | none | define mechanism, benchmark, truthfulness, and approximation guarantee |
