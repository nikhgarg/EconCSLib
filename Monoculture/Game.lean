import Monoculture.Expectation

namespace Monoculture

/-- The two strategy choices in the paper. -/
inductive Strategy where
  | algorithm
  | human
deriving DecidableEq, Repr

/--
A fixed two-strategy instance of the paper's game, after candidate values have been
fixed pointwise. The outer candidate distribution `D` can be added later by placing
a probability distribution on value functions.
-/
structure Model (n : ℕ) where
  algorithmRanking : PMF (Ranking n)
  humanRanking : PMF (Ranking n)
  value : Candidate n → ℝ

namespace Model

def rankingDist {n : ℕ} (M : Model n) : Strategy → PMF (Ranking n)
  | .algorithm => M.algorithmRanking
  | .human => M.humanRanking

/-- Utility when the labeled firm is first to choose. -/
noncomputable def firstMoverEU {n : ℕ} (M : Model n) (s : Strategy) : ℝ :=
  expectedFirstMoverUtility (M.rankingDist s) M.value

/--
Utility when the labeled first mover uses `s₁`
and the labeled second mover uses `s₂`.
-/
noncomputable def secondMoverEU {n : ℕ} (M : Model n) (s₁ s₂ : Strategy) : ℝ :=
  expectedSecondMoverIndependent (M.rankingDist s₂) (M.rankingDist s₁) M.value

/-- Social welfare for the ordered game in which the `s₁`-firm hires first. -/
noncomputable def welfareOrdered {n : ℕ} (M : Model n) (s₁ s₂ : Strategy) : ℝ :=
  expectedWelfareOrdered (M.rankingDist s₂) (M.rankingDist s₁) M.value

/-- Ex ante welfare when the order of the two labeled firms is uniform. -/
noncomputable def welfareRandomOrder {n : ℕ} (M : Model n) (s₁ s₂ : Strategy) : ℝ :=
  (welfareOrdered M s₁ s₂ + welfareOrdered M s₂ s₁) / 2

/-- Under a symmetric profile, random-order welfare coincides with ordered welfare. -/
theorem welfareRandomOrder_self {n : ℕ} (M : Model n) (s : Strategy) :
    welfareRandomOrder M s s = welfareOrdered M s s := by
  unfold welfareRandomOrder
  ring

/-- The algorithmic strategy is strictly dominant in the induced `2 × 2` game. -/
noncomputable def AlgorithmStrictlyDominant {n : ℕ} (M : Model n) : Prop :=
  let A := Strategy.algorithm
  let H := Strategy.human
  (firstMoverEU M A + secondMoverEU M A A > firstMoverEU M H + secondMoverEU M A H) ∧
  (firstMoverEU M A + secondMoverEU M H A > firstMoverEU M H + secondMoverEU M H H)

/-- The all-human profile yields higher welfare than the all-algorithmic profile. -/
noncomputable def HumanProfileBeatsAlgorithmProfile {n : ℕ} (M : Model n) : Prop :=
  welfareRandomOrder M Strategy.human Strategy.human >
    welfareRandomOrder M Strategy.algorithm Strategy.algorithm

/--
A fixed-parameter instance of the paper's paradox:
the algorithm is strictly dominant, but the all-human profile has higher welfare.
-/
noncomputable def HasMonocultureParadox {n : ℕ} (M : Model n) : Prop :=
  AlgorithmStrictlyDominant M ∧ HumanProfileBeatsAlgorithmProfile M

end Model
end Monoculture
