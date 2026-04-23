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

The broader EC Test-of-Time track has also started:

- `EconCSLean/FairDivision/*` for the 2025 Test-of-Time indivisible-goods paper
- `EconCSLean/Auction/*` for the 2021 digital-goods auction paper and later
  auction papers

## Current Continuation Target

The main active continuation target from the imported track is still the
monoculture/Mallows branch through:

```lean
MallowsComparison.CenterMallowsCertificate
MallowsComparison.centerProbabilityCertificate_of_centerMallowsCertificate
MallowsComparison.paperHypotheses_of_centerProbabilityCertificate
```

The below-one center-probability obligations are now proved from Mallows support
using the top-two-swapped ranking. The useful next work is to prove the remaining
finite Mallows comparison and candidatewise nonnegativity inequalities, not to
start a new continuous branch.

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

This imported code is aligned to Lean/mathlib `v4.29.0`.

```bash
lake build
```

## Repository Direction

The imported decision/fairness/recommendation track is not the whole project.
It is the first substantial batch of paper formalization work inside
`EconCSLean`, and it should inform how the broader library grows.

That broader roadmap lives in [ROADMAP.md](ROADMAP.md).
