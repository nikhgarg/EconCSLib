import EconCSLib.Applications.RecommenderSystems.Policy
import EconCSLib.Applications.RecommenderSystems.Allocation
import EconCSLib.Applications.RecommenderSystems.AllocationSequence
import EconCSLib.Applications.RecommenderSystems.Classwise
import EconCSLib.Applications.RecommenderSystems.PolicyAveraging
import EconCSLib.Applications.RecommenderSystems.TopKOracle

/-!
# Recommender-System Applications

Aggregate import for reusable recommender-system primitives.

## Main declarations

- `EconCSLib.Applications.RecommenderSystems.Policy`: finite recommendation
  policies, supports, and fairness primitives.
- `EconCSLib.Applications.RecommenderSystems.Allocation`: finite count
  allocations and support/count algebra.
- `EconCSLib.Applications.RecommenderSystems.AllocationSequence`: feasible and
  optimal allocation sequences, target-profile convergence, sublinear
  scaled-count profile bridges, and certificate-shaped wrappers for pairwise
  scaled-count/FOC/eventual floor arguments.
- `EconCSLib.Applications.RecommenderSystems.Classwise`: classwise and
  type-indexed aggregation helpers.
- `EconCSLib.Applications.RecommenderSystems.PolicyAveraging`: averaging
  finite policy kernels over finite groups.
-/
