# EconCSLean

`EconCSLean` is a Lean 4 library for formalizing results that matter to the
economics-and-computation community.

The long-term project still has three linked goals:

1. formalize canonical EC-style papers,
2. extract reusable library primitives for that community,
3. eventually turn the workflow into an agent skill for new papers.

## Current Imported Track

This repository now includes an imported discrete formalization track covering
three papers:

- Sophie Greenwood, Sudalakshmee Chiniah, and Nikhil Garg,
  *User-item fairness tradeoffs in recommendations*
- Kenny Peng, Manish Raghavan, Emma Pierson, Jon Kleinberg, and Nikhil Garg,
  *Reconciling the diversity-aware recommendation trade-off in recommendations*

That imported track is organized around one reusable finite/discrete core:

- `DecisionCore/*` for shared randomized-policy and allocation infrastructure
- `UserItemFairness/*` for the fairness paper
- `AccuracyDiversity/*` for the diversity-aware recommendation paper

Each paper folder now follows the same audit pattern:

- `README.md` records the exact paper source version and theorem-status table.
- `MainTheorems.lean` is the central human-readable theorem interface.
- Detailed proof files stay in the folder and are imported by the central file.

The broader EC Test-of-Time track has also started:

- `EconCSLean/Graph/*` for reusable finite directed-relation/cycle lemmas
- `EconCSLean/Math/*` for reusable algebraic proof helpers
- `EconCSLean/FairDivision/*` for the 2025 Test-of-Time indivisible-goods paper
- `EconCSLean/Auction/*` for the 2021 digital-goods auction paper and later
  auction papers

## Current Continuation Target

The main active continuation target from the imported track is still the
monoculture/Mallows branch through:

```lean
MallowsComparison.CenterMallowsCertificate
MallowsComparison.CenterMallowsFiniteSumCertificate
MallowsComparison.centerMallowsFiniteSumCertificate_of_candidateSumCertificate
MallowsComparison.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
MallowsComparison.CenterMallowsProductCrossWeightCertificate
MallowsComparison.CenterMallowsReducedProductCrossWeightCertificate
MallowsComparison.paperHypotheses_of_centerMallowsProductCrossWeightCertificate
MallowsComparison.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate
```

The below-one center-probability obligations are now proved from Mallows support
using the top-two-swapped ranking. The preferred continuation target is now the
sum-level finite Mallows certificate, because non-center first-choice fibers can
have negative gap mass and should not be forced into candidatewise
nonnegativity assumptions.

Other current theorem anchors:

- `EconCSLean.FairDivision.lmms_theorem_2_1_finite_maxMarginal`
- `ReductionWitness.symmetricOptimalItemFairness_eq_reduced`
- `ReductionWitness.exists_reducedOptimalAtLevel_of_original_symmetric_optimal`
- `ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum`
- `BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum`

## Orientation

If you are new to the imported code, start with:

- [docs/START_HERE_FOR_HUMANS.md](docs/START_HERE_FOR_HUMANS.md)
- [HumanStartHere.lean](HumanStartHere.lean)
- [docs/ECONCSLEAN_CURRENT_STATUS.md](docs/ECONCSLEAN_CURRENT_STATUS.md)
- [docs/PAPER_MAP.md](docs/PAPER_MAP.md)
- [docs/DECISION_FAIRNESS_HANDOFF.md](docs/DECISION_FAIRNESS_HANDOFF.md)
- [docs/EC_TEST_OF_TIME_FORMALIZATION_PLAN.md](docs/EC_TEST_OF_TIME_FORMALIZATION_PLAN.md)
- [skills/econcs-formalizer/SKILL.md](skills/econcs-formalizer/SKILL.md)

## Build

This code is aligned to Lean/mathlib/CSLib `v4.30.0-rc2`.

```bash
lake build EconCSLean
```

## GitHub Automation

The repository keeps CI and manual dependency-update workflows under
`.github/workflows`. Release-tag/release-publishing automation has been removed;
releases should be cut manually if needed.

## Repository Direction

The imported decision/fairness/recommendation track is not the whole project.
It is the first substantial batch of paper formalization work inside
`EconCSLean`, and it should inform how the broader library grows.

That broader roadmap lives in [ROADMAP.md](ROADMAP.md).
