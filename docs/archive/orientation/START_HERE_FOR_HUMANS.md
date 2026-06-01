# Start Here If You Do Not Know Lean

This is the human-oriented entrance to the imported formalization track.

The current imported code has three paper tracks built on one reusable discrete
core:

- `Monoculture/*` for the algorithmic monoculture paper
- `UserItemFairness/*` for the user-item fairness paper
- `AccuracyDiversity/*` for the accuracy-diversity paper
- `DecisionCore/*` for the shared infrastructure

The fastest way to get oriented is:

1. open `HumanStartHere.lean`
2. then open `Monoculture/Basic.lean`
3. then open `UserItemFairness/Basic.lean`
4. then open `AccuracyDiversity/Basic.lean`
5. only after that read the heavier theorem files

## Minimal Lean Mental Model

The main things you need at first are:

- `def`: defines an object
- `theorem`: states and proves a fact
- `example`: a small local theorem
- `namespace`: groups names together
- `#check`: asks Lean for the type of something

A theorem in Lean is just an object whose type is a proposition.

## How To Read This Repo

Start from simple data, not from the hardest theorem.

Best beginner files:

- `HumanStartHere.lean`
- `Monoculture/Basic.lean`
- `UserItemFairness/Basic.lean`
- `AccuracyDiversity/Basic.lean`

Each paper folder also has:

- `README.md`, with the exact paper source version and theorem-status table
- `MainTheorems.lean`, with the central paper-facing theorem statements

Then read the shared layer:

- `DecisionCore/FiniteExpectation.lean`
- `DecisionCore/FiniteSigns.lean`
- `DecisionCore/Policy.lean`
- `DecisionCore/Conditional.lean`
- `DecisionCore/Classwise.lean`
- `DecisionCore/Allocation.lean`

Then move to one paper-specific proof path at a time.

## Best Current Monoculture Entry Point

The current best entry point for the monoculture continuation is:

- `Monoculture/MallowsFiniteLemmas.lean`

The key theorem interfaces are:

- `MallowsComparison.CenterPositiveCertificate`
- `MallowsComparison.CenterProbabilityCertificate`
- `MallowsComparison.CenterMallowsCertificate`
- `MallowsComparison.CenterMallowsWeightCertificate`
- `MallowsComparison.CenterMallowsFiniteSumCertificate`
- `MallowsComparison.centerMallowsFiniteSumCertificate_of_candidateSumCertificate`
- `MallowsComparison.theorem3_pointwise_of_centerMallowsFiniteSumCertificate`
- `MallowsComparison.CenterMallowsProductCrossWeightCertificate`
- `MallowsComparison.CenterMallowsReducedProductCrossWeightCertificate`
- `MallowsComparison.paperHypotheses_of_centerMallowsCertificate`
- `MallowsComparison.paperHypotheses_of_centerMallowsProductCrossWeightCertificate`
- `MallowsComparison.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate`

The Mallows-specific certificate is the near-term continuation target because
the generic below-one probability fields are already discharged by Mallows
support lemmas. If proving finite inequalities directly, use the finite-sum
target
`MallowsComparison.theorem3_pointwise_of_centerMallowsFiniteSumCertificate`.

The fair-division Test-of-Time theorem is closed at
`EconCSLib.FairDivision.lmms_theorem_2_1_finite_maxMarginal`. The imported
fairness and accuracy-diversity tracks now have two-sided conditional LP
reduction and finite exchange first-order conditions, respectively; see
`HumanStartHere.lean` for the current `#check` anchors.
