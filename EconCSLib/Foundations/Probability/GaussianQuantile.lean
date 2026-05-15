import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Ring.Real
import EconCSLib.Foundations.Probability.Gaussian

/-!
# Standard Gaussian Quantile Interface

Small analytic interface for papers that use the inverse standard-normal CDF.

## Main declarations

- `StandardGaussianQuantileAPI`
- `StandardGaussianQuantileAPI.quantile_pos_of_two_mul_capacity_lt_mass`
-/

namespace EconCSLib
namespace Probability

/--
Analytic API for the inverse standard-normal CDF.

The concrete construction of `Φ⁻¹` is intentionally kept behind this narrow
interface until the repository has a full measure-theoretic normal CDF.  Paper
proofs can still discharge their algebraic and monotonicity obligations using
only monotonicity, continuity, and positivity above the median.
-/
structure StandardGaussianQuantileAPI where
  cdfAPI : StandardGaussianCDFAPI
  quantile : ℝ → ℝ
  quantile_mono : Monotone quantile
  quantile_continuous : Continuous quantile
  quantile_pos_of_half_lt : ∀ {p : ℝ}, (1 / 2 : ℝ) < p → 0 < quantile p

namespace StandardGaussianQuantileAPI

/--
The paper's selectivity condition relative to an eligible mass,
`2 * capacity < mass`, makes the upper-tail quantile
`Φ⁻¹(1 - capacity / mass)` positive.
-/
theorem quantile_pos_of_two_mul_capacity_lt_mass
    (Q : StandardGaussianQuantileAPI)
    {capacity mass : ℝ}
    (hmass_pos : 0 < mass) (hselective : 2 * capacity < mass) :
    0 < Q.quantile (1 - capacity / mass) := by
  have hdiv_lt_half : capacity / mass < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hmass_pos]
    linarith
  exact Q.quantile_pos_of_half_lt (by linarith)

end StandardGaussianQuantileAPI

end Probability
end EconCSLib
