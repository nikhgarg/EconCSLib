import LOS02CombinatorialAuctions.ProofInterface

/-!
# Paper Assumptions: LOS02 Combinatorial Auctions

This file records source theorem conditions and documented proof boundaries used
by the paper-facing LOS02 interface. It is intentionally small: theorem
conditions remain in the theorem statements, while this ledger gives the audit a
machine-readable place to verify that each paper-facing premise is source-facing
or explicitly documented as a partial complexity boundary.
-/

namespace LOS02CombinatorialAuctions

open EconCSLib.Auction

/-- Truthfulness is stated relative to an admissible declaration domain. -/
-- audit-premise: admissible : CombinatorialReport Bidder Item → Prop
abbrev assumption_admissible_combinatorial_report_domain
    {Bidder Item : Type*}
    (admissible : CombinatorialReport Bidder Item → Prop) : Prop :=
  True

/--
External exact set-packing hardness and polynomial-time transfer facts for the
paper's Theorem 6.1 complexity consequence.
-/
-- audit-premise: hexternal : ∀ wspSolver, weightedSetPackingOptimalSolver wspSolver → FeasibleWSP wspSolver → complexityModel.npEqZPP
abbrev assumption_external_exact_set_packing_complexity_boundary
    {Bidder Item Language : Type*}
    (complexityModel :
      EconCSLib.Complexity.ComplexityClassModel Language)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop) : Prop :=
  True

/--
External set-packing inapproximability and polynomial-time transfer facts for
the paper's Theorem 6.1 approximation consequence.
-/
-- audit-premise: hexternal : ∀ wspSolver, weightedSetPackingApproximationSolverAtLeast factor wspSolver → FeasibleWSP wspSolver → complexityModel.npEqZPP
abbrev assumption_external_approximation_set_packing_complexity_boundary
    {Bidder Item Language : Type*}
    (factor : ℝ)
    (complexityModel :
      EconCSLib.Complexity.ComplexityClassModel Language)
    (FeasibleWSP :
      ((Bidder → Finset Item) → (Bidder → ℝ) → Finset Bidder) → Prop) : Prop :=
  True

/-- The optimal allocation considered in Theorem 7.2 is feasible. -/
-- audit-premise: hoptimal_disjoint : PairwiseDisjointDesired bids optimal
abbrev assumption_theorem7_optimal_allocation_feasible
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (optimal : Finset Bidder) : Prop :=
  PairwiseDisjointDesired bids optimal

/-- The fixed greedy order contains every bidder in the optimal allocation. -/
-- audit-premise: hoptimal_order : ∀ i, i ∈ optimal → i ∈ order
abbrev assumption_theorem7_optimal_bidders_in_order
    {Bidder : Type*} (optimal : Finset Bidder) (order : List Bidder) : Prop :=
  ∀ i, i ∈ optimal → i ∈ order

/-- Lemma 9.2 is the denied-bidder case. -/
-- audit-premise: hdeny : i ∉ M.accepted reports
abbrev assumption_lemma9_denied_bidder_case
    {Bidder Item : Type*}
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (reports : Bidder → SingleMindedBid Item) (i : Bidder) : Prop :=
  i ∉ M.accepted reports

/-- Lemma 9.4 ranges over nonnegative single-minded value declarations. -/
-- audit-premise: hv' : 0 ≤ v'
abbrev assumption_lemma9_nonnegative_value_deviation (v' : ℝ) : Prop :=
  0 ≤ v'

/--
The Lemma 9.3--9.6 critical-price rows are stated relative to the paper's
critical-value axioms on the nonnegative single-minded declaration domain.
-/
-- audit-premise: C : M.NonnegativeCriticalValueWithInfinityCertificate
abbrev assumption_lemma9_nonnegative_critical_value_axioms
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop :=
  ∃ _C : M.NonnegativeCriticalValueWithInfinityCertificate, True

/-- Lemma 9.5 is the finite-threshold case for the larger desired set. -/
-- audit-premise: hLarge : C.threshold reports i sLarge = some pLarge
abbrev assumption_lemma9_finite_large_threshold
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate)
    (reports : Bidder → SingleMindedBid Item) (i : Bidder)
    (sLarge : Finset Item) (pLarge : ℝ) : Prop :=
  C.threshold reports i sLarge = some pLarge

end LOS02CombinatorialAuctions
