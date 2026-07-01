import KR21Monoculture.PaperDefinitions

namespace KR21Monoculture

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
noncomputable def Theorem1Target {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) : Prop := ∃ θA, θH < θA ∧ Model.HasKR21MonocultureParadox (AccuracyFamily.modelAt F θA θH)

/--
Paper-facing theorem statement equivalent.

Theorem 1 (family form) is exactly the existence witness for a higher-accuracy
algorithm parameter where the induced model has a monoculture paradox.
-/
theorem theorem1Target_iff_exists_paradox
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    AccuracyFamily.Theorem1Target F θH ↔
      ∃ θA, θH < θA ∧
        Model.HasKR21MonocultureParadox (AccuracyFamily.modelAt F θA θH) := by
  rfl

end AccuracyFamily
end KR21Monoculture
