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

The mathematically faithful continuity domain for `Φ⁻¹` is the probability
interval `(0,1)`.  Paper proofs should prove their displayed quantile
arguments lie in this interval, then use this narrow interface for monotonicity,
continuity, and positivity above the median.
-/
structure StandardGaussianQuantileAPI where
  cdfAPI : StandardGaussianCDFAPI
  quantile : ℝ → ℝ
  quantile_mono : MonotoneOn quantile (Set.Ioo (0 : ℝ) 1)
  quantile_continuous : ContinuousOn quantile (Set.Ioo (0 : ℝ) 1)
  quantile_pos_of_half_lt :
    ∀ {p : ℝ}, p ∈ Set.Ioo (1 / 2 : ℝ) 1 → 0 < quantile p

namespace StandardGaussianQuantileAPI

/--
The paper's selectivity condition relative to an eligible mass,
`2 * capacity < mass`, makes the upper-tail quantile
`Φ⁻¹(1 - capacity / mass)` positive.
-/
theorem quantile_pos_of_two_mul_capacity_lt_mass
    (Q : StandardGaussianQuantileAPI)
    {capacity mass : ℝ}
    (hcapacity_pos : 0 < capacity)
    (hmass_pos : 0 < mass) (hselective : 2 * capacity < mass) :
    0 < Q.quantile (1 - capacity / mass) := by
  have hdiv_lt_half : capacity / mass < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hmass_pos]
    linarith
  have hdiv_pos : 0 < capacity / mass := div_pos hcapacity_pos hmass_pos
  exact Q.quantile_pos_of_half_lt ⟨by linarith, by linarith⟩

end StandardGaussianQuantileAPI

end Probability
end EconCSLib
