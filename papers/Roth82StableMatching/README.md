# The Economics of Matching: Stability and Incentives

## Source Version

- Paper: *The Economics of Matching: Stability and Incentives*
- Author: Alvin E. Roth
- Version checked locally: Mathematics of Operations Research, Vol. 7, No. 4 (1982)
- Official URL: https://doi.org/10.1287/moor.7.4.617
- Public PDF: https://pubsonline.informs.org/doi/epdf/10.1287/moor.7.4.617

The PDF is cached locally as `Roth82StableMatching.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache `Roth82StableMatching.txt`
is used for named-statement searches; refresh it only if the source PDF changes.

## Central Theorem File

- `Roth82StableMatching/MainTheorems.lean`

Detailed reusable matching and deferred-acceptance primitives live in
`EconCSLib/Markets/Matching`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Paper definitions: matching utilities, stability, men-optimality, one-sided truthfulness | `paper_matching_valM`, `paper_matching_valW`, `paper_is_stable`, `paper_is_men_optimal`, `paper_truthful_for_men` | formalized definitions | `Roth82StableMatching/MainTheorems.lean` | finite two-sided matching model |
| Theorem 1, stable outcomes are nonempty | `paper_roth82_theorem1_stable_outcome_exists` | conditional | `Roth82StableMatching/MainTheorems.lean` | requires `DaProducesStableMatchingCertificate` for the deferred-acceptance output |
| Theorem 2, men- and women-optimal stable outcomes exist | `paper_roth82_theorem2_men_optimal_stable_outcome` | partial conditional | `Roth82StableMatching/MainTheorems.lean` | men side requires `DaProducesStableMatchingCertificate` and `DaIsMenOptimalCertificate`; symmetric women side not wrapped |
| Theorem 3, no stable procedure is strategyproof for all agents | none | not started | none | requires finite counterexample and arbitrary stable-procedure model |
| Theorem 4, efficient strategyproof procedures exist | none | not started | none | requires Pareto-efficiency procedure model |
| Theorem 5, one-sided truthfulness of optimal stable procedure | `paper_roth82_theorem5_men_truthful` | conditional | `Roth82StableMatching/MainTheorems.lean` | requires `DaTruthfulForMenCertificate` |
| Corollary 5.1, opposite side cannot profit by misrepresenting first choice | none | not started | none | requires source Lemmas 1--2 and misrepresentation model |
| Lemma 1, simple misrepresentation partner equivalence | none | not started | none | requires preference-profile transformation model |
| Lemma 2, successful simple misrepresentation does not hurt other men | none | not started | none | requires stepwise DA proposal trace |
| Theorem 6, men-optimal stable outcome is weakly Pareto optimal for men | none | not started | none | requires feasible-outcome Pareto comparison |
| Theorem 7, no stable procedure prevents all `k`th-choice manipulation | none | not started | none | requires generalized manipulation counterexample |

## Source-Audit Notes

The cached text contains Theorems 1--7, Corollary 5.1, and Lemmas 1--2. The
previous README incorrectly treated the one-sided DA truthfulness wrapper as
source Theorem 3; source Theorem 3 is an impossibility theorem and remains open.
Current Lean coverage is a conditional deferred-acceptance scaffold, not a
complete proof of the Roth 1982 theorem sequence.
