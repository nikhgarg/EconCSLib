import Monoculture.PaperDefinitions

namespace Monoculture

/--
A one-parameter family of ranking distributions together with a fixed pointwise
value function. This is the level at which the paper's `θ ↦ F_θ` lives.
-/
structure AccuracyFamily (n : ℕ) where
  dist : ℝ → PMF (Ranking n)
  value : Candidate n → ℝ

namespace AccuracyFamily

/--
The two-strategy model induced by using accuracy `θA` for the algorithm and
accuracy `θH` for the human ranking.
-/
noncomputable def modelAt {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : Model n where
  algorithmRanking := F.dist θA
  humanRanking := F.dist θH
  value := F.value

/--
The theorem-1 target for a fixed `θH`: there exists a better algorithmic accuracy
`θA > θH` that creates the monoculture paradox.
-/
noncomputable def Theorem1Target {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) : Prop :=
  ∃ θA, θH < θA ∧ Model.HasMonocultureParadox (AccuracyFamily.modelAt F θA θH)

end AccuracyFamily
end Monoculture
