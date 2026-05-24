import EconCSLib.Foundations.Optimization.Approximation
import EconCSLib.Foundations.Optimization.Argmax
import EconCSLib.Foundations.Optimization.ChoiceEquilibrium
import EconCSLib.Foundations.Optimization.ChoiceEquilibriumAE
import EconCSLib.Foundations.Optimization.BinaryChoice
import EconCSLib.Foundations.Optimization.BinaryChoiceAE
import EconCSLib.Foundations.Optimization.Certificate
import EconCSLib.Foundations.Optimization.Endpoint
import EconCSLib.Foundations.Optimization.FiniteSearch
import EconCSLib.Foundations.Optimization.LinearProgram
import EconCSLib.Foundations.Optimization.MoveGraph

/-!
# Optimization Foundations

Aggregate import for reusable optimization primitives.

## Main declarations

- `EconCSLib.Foundations.Optimization.Argmax`: finite argmax, pointwise
  maximization, and finite linear expectation interfaces used by classification,
  recommendation, and decision-rule papers.
- `EconCSLib.Foundations.Optimization.ChoiceEquilibrium`: static
  choice-equilibrium data, weak best-response, and consistency projections.
- `EconCSLib.Foundations.Optimization.ChoiceEquilibriumAE`: almost-everywhere
  best-response variant for continuous or mixed information laws.
- `EconCSLib.Foundations.Optimization.BinaryChoice`: two-sided binary
  best-response predicates and basic contradiction lemmas.
- `EconCSLib.Foundations.Optimization.BinaryChoiceAE`: a.e. binary
  best-response predicates and affine cutoff consequences.
- `EconCSLib.Foundations.Optimization.Approximation`: primal-dual/benchmark
  sandwich certificates for approximation and competitive-ratio proofs.
- `EconCSLib.Foundations.Optimization.Certificate`: reusable optimality
  certificates for maximization/minimization arguments over explicit feasible
  sets.
- `EconCSLib.Foundations.Optimization.Endpoint`: one-dimensional endpoint-move
  calculus from derivative signs, including first/last-zero stopping lemmas.
- `EconCSLib.Foundations.Optimization.FiniteSearch`: existence of optimizers
  over nonempty finite feasible sets and finite encodings of feasible regions.
- `EconCSLib.Foundations.Optimization.LinearProgram`: lightweight finite LP
  primal/dual feasibility, weak duality, and optimality certificates.
- `EconCSLib.Foundations.Optimization.MoveGraph`: exchange/local-move
  optimality from reachability and monotone moves.
-/
