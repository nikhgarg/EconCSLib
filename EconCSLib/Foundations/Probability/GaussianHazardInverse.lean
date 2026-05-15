import EconCSLib.Foundations.Probability.Gaussian

/-!
# Gaussian Hazard Inverse Interface

Small interface for papers that use the inverse normal hazard rate.

## Main declarations

- `GaussianHazardInverseCertificate`
-/

namespace EconCSLib
namespace Probability

/--
Analytic certificate for an inverse of the standard-normal hazard rate.

The base `GaussianHazardCertificate` already exposes the hazard rate and its
monotonicity.  This extension adds exactly the order-theoretic inverse fact
used by admissions/testing papers that write thresholds with `HR⁻¹`.
-/
structure GaussianHazardInverseCertificate extends GaussianHazardCertificate where
  hazardInv : ℝ → ℝ
  hazard_le_iff_le_inv : ∀ {z y : ℝ}, hazard z ≤ y ↔ z ≤ hazardInv y

end Probability
end EconCSLib
