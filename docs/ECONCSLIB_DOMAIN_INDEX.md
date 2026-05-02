# EconCSLib Domain Index

This file tracks where reusable declarations live and where to start reading
when you need material from a domain quickly.

## Foundations

- Entrypoint: `EconCSLib.Foundations.Math`, `EconCSLib.Foundations.Graph`
- Modules:
  - `EconCSLib.Foundations.Math`:
    `FiniteSum`, `FiniteRanking`, `FiniteRounding`, `FiniteSigns`,
    `Sequence`, `Asymptotics`, `IntervalCrossing`,
    `EpsilonContinuity`, `PositiveDenominator`
  - `EconCSLib.Foundations.Graph`
  - `EconCSLib.Foundations.Probability`
    (`FiniteExpectation`, `Kernel`, `Conditional`, `MarkovChain`, `MDP`,
    `StochasticDominance`, `MeasureInequalities`, `Admissions`, `FairCoin`)
  - `EconCSLib.Foundations.Econometrics.RatingModels`

## Applications

- Entrypoint: `EconCSLib.Applications.RecommenderSystems.Policy`
- Modules:
  - `Policy`, `Allocation`
  - `Classwise`, `PolicyAveraging`

## Mechanism Design

- Entrypoint: `EconCSLib.MechanismDesign.Auctions`
- Modules:
  - `DigitalGoods`, `Position`, `Combinatorial`
  - `EconCSLib.MechanismDesign.Auctions.MainTheorems`

## Markets

- Entrypoint: `EconCSLib.Markets.Matching`
- Modules:
  - `Matching/Basic`, `Matching/DeferredAcceptance`

## Learning

- Entrypoint: `EconCSLib.Learning.Bandits.ThompsonSampling`
- Modules:
  - Bayesian-bandit primitives and posterior update lemmas used by papers

## Algorithms

- Entrypoints: `EconCSLib.Algorithms.Online`, `EconCSLib.Algorithms.Complexity.Yao`
- Modules:
  - `Online/AdWords`, `Online/Regret`

## Social Choice

- Entrypoint: `EconCSLib.SocialChoice.FairDivision`
- Modules:
  - `FairDivision/IndivisibleGoods`, `LMMSAlgorithm`

## Navigation tips

- Use the domain entrypoint as the first import from that area.
- Then import narrower modules only when you need paper-specific helper lemmas.
- New reusable theorems should land under `EconCSLib/`; paper-specific proof
  code should remain in `papers/`.
