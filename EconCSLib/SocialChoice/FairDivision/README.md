# On Approximately Fair Allocations of Indivisible Goods

## Source Version

- Paper: *On Approximately Fair Allocations of Indivisible Goods*
- Authors: Richard J. Lipton, Evangelos Markakis, Elchanan Mossel, and Amin Saberi
- Version formalized: EC 2004 paper, ACM DOI 10.1145/988772.988792
- Official URL: https://dl.acm.org/doi/10.1145/988772.988792
- Official PDF: https://dl.acm.org/doi/pdf/10.1145/988772.988792
- Public course PDF mirror: https://www.cs.cmu.edu/~arielpro/15896s15/docs/paper12a.pdf
- Accessed: 2026-04-23

The PDF is not committed to git. Use the ACM DOI/PDF above as the source
version; the public mirror is listed only for easier access.

## Central Theorem File

- `EconCSLib/FairDivision/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Detailed envy-graph,
cycle-elimination, potential, and allocation lemmas live in
`IndivisibleGoods.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Monotone valuation, allocation, envy, and bounded envy definitions | `Valuation`, `IsAllocationOf`, `envy`, `EnvyBoundedBy` | formalized | `EconCSLib/FairDivision/IndivisibleGoods.lean` | none |
| Acyclic envy graph gives an unenvied agent | `exists_noOneEnvies_of_acyclicEnvyGraph` | formalized | `EconCSLib/FairDivision/IndivisibleGoods.lean` | nonempty agent type |
| Finite envy-cycle extraction | `hasEnvyCycleListExtraction_of_finite` | formalized | `EconCSLib/FairDivision/IndivisibleGoods.lean` | none |
| Theorem 2.1, abstract marginal-bound form | `paper_lmms_theorem_2_1_marginal_bound` | formalized | `EconCSLib/FairDivision/MainTheorems.lean` | finite agents/items and marginal bound |
| Theorem 2.1, maximum-marginal form | `paper_lmms_theorem_2_1_max_marginal` | formalized | `EconCSLib/FairDivision/MainTheorems.lean` | finite nonempty agents/items |
| Polynomial-time algorithm claim | none | not started | none | executable algorithm and complexity model |
