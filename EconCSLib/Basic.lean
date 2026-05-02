import EconCSLib.Foundations.Graph
import EconCSLib.Foundations.Math
import EconCSLib.Foundations.Optimization.Argmax
import EconCSLib.Foundations.Probability.Admissions
import EconCSLib.Foundations.Probability.Conditional
import EconCSLib.Foundations.Probability.FairCoin
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.Foundations.Probability.Kernel
import EconCSLib.Foundations.Probability.MarkovChain
import EconCSLib.Foundations.Probability.MDP
import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.Foundations.Probability.StochasticDominance
import EconCSLib.Foundations.Econometrics.RatingModels.BinaryRating
import EconCSLib.Foundations.Econometrics.RatingModels.OrdinalRating
import EconCSLib.Algorithms.Online
import EconCSLib.Algorithms.Complexity.Yao
import EconCSLib.Algorithms.Online.AdWords
import EconCSLib.Algorithms.Online.Regret
import EconCSLib.Learning.Bandits.ThompsonSampling
import EconCSLib.MechanismDesign.Auctions
import EconCSLib.MechanismDesign.Auctions.MainTheorems
import EconCSLib.SocialChoice.FairDivision
import EconCSLib.Markets.Matching
import EconCSLib.Applications.RecommenderSystems.Policy
import EconCSLib.Applications.RecommenderSystems.Classwise
import EconCSLib.Applications.RecommenderSystems.Allocation
import EconCSLib.Applications.RecommenderSystems.PolicyAveraging
import EconCSLib.Foundations.Math.FiniteSigns
import EconCSLib.Foundations.Math.IntervalCrossing
import EconCSLib.Foundations.Math.EpsilonContinuity

/-!
# EconCSLib Shared Prelude

This file is the shared Lean prelude for reusable library development and paper-facing
proofs. It centralizes the common `import`s and namespace defaults so new files can
start from one stable foundation.

## Main declarations

- `EconCSLib.Basic`: imports the standard `EconCSLib` reusable surface used across the library.
- Shared namespace defaults (`open scoped BigOperators`) for concise theorem scripts.
- A curated aggregate import set to reduce fragile per-file import drift across papers.
-/

open scoped BigOperators
