import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.Applications.RecommenderSystems.Policy

namespace EconCSLib
namespace Online

open scoped BigOperators

/--
Total expected regret over a finite time horizon `T` for a sequence of chosen PMFs `pi`,
given true qualities `q` and available sets `M`.
-/
noncomputable def expectedRegret {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (T : ℕ)
    (M : Fin T → Finset V)
    (h_nonempty : ∀ t, (M t).Nonempty)
    (q : V → ℝ)
    (pi : (t : Fin T) → PMF V) : ℝ :=
  ∑ t : Fin T, ((M t).sup' (h_nonempty t) q - EconCSLib.pmfExp (pi t) q)

end Online
end EconCSLib
