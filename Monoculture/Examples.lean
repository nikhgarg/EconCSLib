import Monoculture.Family

namespace Monoculture

/-- A deterministic identity ranking on two candidates. -/
def twoCandidateIdentity : Ranking 0 :=
  Equiv.refl _

/-- The unique nontrivial ranking on two candidates. -/
def twoCandidateSwap : Ranking 0 :=
  Equiv.swap 0 1

/--
A toy value function on two candidates:
candidate `0` is worth `10`, candidate `1` is worth `0`.
-/
def twoCandidateValue : Candidate 0 → ℝ :=
  fun i => if i = 0 then 10 else 0

/--
A minimal deterministic model useful for smoke-testing notation.
It is not intended to witness the paper's paradox.
-/
noncomputable def toyModel : Model 0 where
  algorithmRanking := PMF.pure twoCandidateIdentity
  humanRanking := PMF.pure twoCandidateSwap
  value := twoCandidateValue

/--
A toy family: nonnegative accuracy uses the identity ranking, negative accuracy
uses the swapped ranking.
-/
noncomputable def toyFamily : AccuracyFamily 0 where
  dist θ := if θ ≥ 0 then PMF.pure twoCandidateIdentity else PMF.pure twoCandidateSwap
  value := twoCandidateValue

end Monoculture
