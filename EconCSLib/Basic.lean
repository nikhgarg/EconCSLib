import EconCSLib.Foundations
import EconCSLib.Algorithms.Complexity.Classes
import EconCSLib.Algorithms.Online
import EconCSLib.Algorithms.Complexity.Yao
import EconCSLib.Algorithms.Online.AdWords
import EconCSLib.Algorithms.Online.Regret
import EconCSLib.Learning.Statistics
import EconCSLib.Learning.Bandits.ThompsonSampling
import EconCSLib.MechanismDesign.Auctions
import EconCSLib.SocialChoice
import EconCSLib.Markets.Matching
import EconCSLib.Applications.AlgorithmicFairness
import EconCSLib.Applications.Admissions
import EconCSLib.Applications.RecommenderSystems

/-!
# EconCSLib Shared Prelude

This file is the shared Lean prelude for reusable library development and paper-facing
proofs. It centralizes the common `import`s and namespace defaults so new files can
start from one stable foundation.

## Main declarations

- `EconCSLib.Basic`: imports the standard `EconCSLib` reusable surface used across the library.
- Shared namespace defaults (`open scoped BigOperators`) for concise theorem scripts.
- A curated aggregate import set to reduce fragile per-file import drift across papers.
- Admissions policy/equilibrium surfaces used by testing, matching, and
  strategic admissions formalizations.
-/

open scoped BigOperators
