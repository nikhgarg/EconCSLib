# Truth Revelation in Approximately Efficient Combinatorial Auctions

Machine-readable status source: [`status.json`](status.json).

## Source Version

- Paper: *Truth Revelation in Approximately Efficient Combinatorial Auctions*
- Authors: Daniel Lehmann, Liadan Ita O'Callaghan, and Yoav Shoham
- Version checked locally: Journal of the ACM 49(5), 2002
- DOI: https://doi.org/10.1145/585265.585266
- Public PDF mirror: https://jmvidal.cse.sc.edu/library/lehmann02a.pdf

The PDF is cached locally as `LOS02CombinatorialAuctions.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache
`LOS02CombinatorialAuctions.txt` is used for named-statement searches; refresh
it only if the source PDF changes.

## Central Theorem File

- `LOS02CombinatorialAuctions/MainTheorems.lean`
- `FINAL_VALIDATION_REPORT.md` records the current source inventory,
  proof-boundary audit, and validation commands.
- `START_HERE_NEXT_AGENT.md` points to the current handoff and proof path
  forward.

Reusable combinatorial-auction primitives live in
`EconCSLib/MechanismDesign/Auctions`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Definitions 3.1--3.2, direct mechanism and truthfulness | `CombinatorialAuction`, `paper_combinatorial_truthful_on` | formalized | `LOS02CombinatorialAuctions/MainTheorems.lean` | None; status note: formalized support; finite bidder/item model |
| Theorem 4.1, GVA is truthful | `PaperInterface.theorem4_1_generalized_vickrey_truthful` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean` | None; GVA represented by a welfare-maximizing allocation-rule certificate and Clarke pivot payments |
| Proposition 4.2, truthful GVA bidder utility nonnegative | `PaperInterface.proposition4_2_generalized_vickrey_truthful_utility_nonneg` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean` | None; assumes the source type-space condition that bundle values are nonnegative |
| Definition 5.1, single-minded bidder | `SingleMindedBid`, `IsNonemptySingleMindedProfile` | formalized | `EconCSLib/MechanismDesign/Auctions/Combinatorial.lean` | None; status note: formalized support; finite bundle model |
| Theorem 6.1, set-packing encoding primitives | `PaperInterface.theorem6_1_set_packing_feasibility_encoding_correct`, `PaperInterface.theorem6_1_set_packing_value_encoding_correct` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean` | None; the source identification of weighted set packing with encoded single-minded welfare preserves feasibility and objective value exactly |
| Theorem 6.1, set-packing, independent-set, and clique allocation reductions | `PaperInterface.theorem6_1_weighted_set_packing_reduction`, `ProofInterface.theorem6_1_optimal_solver_reduction`, `ProofInterface.theorem6_1_approximation_preserving_reduction`, `ProofInterface.theorem6_1_approximation_solver_reduction`, `ProofInterface.theorem6_1_decision_problem_encoding_correct`, `ProofInterface.theorem6_1_decision_problem_reduction`, `ProofInterface.theorem6_1_polynomial_time_decision_problem_reduction`, `ProofInterface.theorem6_1_set_packing_hardness_transfers_to_single_minded`, `ProofInterface.theorem6_1_clique_decision_complement_independent_set_reduction`, `ProofInterface.theorem6_1_independent_set_decision_set_packing_reduction`, `ProofInterface.theorem6_1_clique_decision_set_packing_reduction`, `PaperInterface.theorem6_1_clique_decision_single_minded_welfare_reduction`, `ProofInterface.theorem6_1_clique_hardness_transfers_to_single_minded`, `ProofInterface.theorem6_1_graph_independent_set_feasibility_reduction`, `ProofInterface.theorem6_1_independent_set_set_packing_reduction`, `ProofInterface.theorem6_1_independent_set_allocation_reduction`, `ProofInterface.theorem6_1_clique_complement_independent_set_reduction`, `ProofInterface.theorem6_1_clique_complement_set_packing_reduction`, `ProofInterface.theorem6_1_clique_complement_allocation_reduction` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; the clique-complement, graph-edge incidence, weighted set-packing, threshold-decision, reduction-closed hardness-transfer, exact solver, and approximation-preserving reductions used by the source proof are represented |
| Theorem 6.1, NP-hardness and NP=ZPP complexity consequences | `ProofInterface.theorem6_1_external_optimal_solver_complexity_consequence`, `ProofInterface.theorem6_1_external_approximation_solver_complexity_consequence`, `PaperInterface.theorem6_1_external_optimal_solver_np_eq_zpp`, `PaperInterface.theorem6_1_external_approximation_solver_np_eq_zpp` | conditional | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | The Karp/Hastad set-packing hardness facts and polynomial-time preservation are supplied externally; Lean now names the abstract `NP = ZPP` consequence through `EconCSLib.Complexity.ComplexityClassModel`, while machine-level class semantics remain outside the current library |
| Complexity-class note after Theorem 6.1 | `ProofInterface.complexity_note_p_eq_np_implies_np_eq_zpp`, `PaperInterface.complexity_note_np_eq_zpp_implies_randomized_collapse` | conditional | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | The class relationships are fields of the abstract `RandomizedComplexityClassModel`; Lean proves the note's collapse implications without claiming machine-level semantics |
| Definition 7.1, average amount per good | `PaperInterface.averageAmountPerGood`, `ProofInterface.averageAmountPerGood_le_of_subset_value_le`, `ProofInterface.sqrtAmountNorm`, `PaperInterface.averageOrderOf`, `ProofInterface.averageValueUpdateWindow`, `ProofInterface.averageValueUpdateWindow_membership_iff_mechanism_of_split` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; also exposes the square-root norm used in Theorem 7.2 and the concrete deterministic average-descending bidder order, including duplicate-freeness, membership, average-descending sortedness, stability after erasing a value-updated bidder, the ordered-insertion suffix window, and the local-to-full mechanism membership equivalence |
| Greedy allocation scheme | `PaperInterface.greedyAcceptedFromOrder`, `ProofInterface.greedyAllocationFromOrder`, `PaperInterface.averageGreedyAcceptedSet`, `ProofInterface.averageGreedyAllocation`, `ProofInterface.averageOrder_greedy_allocation_scheme`, `ProofInterface.greedy_accepted_pairwise_disjoint`, `ProofInterface.averageGreedyAcceptedSet_pairwise_disjoint`, `ProofInterface.greedy_allocation_feasible`, `ProofInterface.averageGreedyAllocation_feasible` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; the explicit-order greedy fold and the concrete average-order instantiation are represented; accepted bids are pairwise disjoint and the induced allocation is feasible when accepted desired bundles lie in the goods set |
| Theorem 7.2, greedy allocation approximation | `ProofInterface.theorem7_2_rejected_bid_has_preceding_sqrt_blocker`, `ProofInterface.theorem7_2_order_blocking_certificate_of_disjoint`, `ProofInterface.theorem7_2_blocking_certificate_normsq_bound`, `PaperInterface.theorem7_2_sqrt_norm_approx_of_sorted_order`, `ProofInterface.theorem7_2_sqrt_norm_approx_of_sorted_order_disjoint`, `ProofInterface.theorem7_2_common_bid_removal_bridge` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; proves the `sqrt(k)` approximation for a sorted explicit greedy order, derives the source proof's blocker/counting and reduced disjoint instance steps, and lifts the bound back by the common-bid add-back bridge |
| Lemmas 9.1--9.5, axioms imply utility/payment properties | `PaperInterface.lemma9_1_exists_nonnegative_critical_value_of_monotonicity`, `PaperInterface.lemma9_2_denied_bidder_utility_eq_zero`, `PaperInterface.lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate`, `PaperInterface.lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms`, `PaperInterface.lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean` | None; Lemma 9.1 constructs finite-or-infinite acceptance thresholds from monotonicity on the source nonnegative domain, while the later Critical/payment certificate supplies payment equality to those thresholds |
| Theorem 9.6, Exactness/Monotonicity/Participation/Critical imply truthfulness | `ProofInterface.theorem9_6_single_minded_truthful_of_infinity_axioms`, `PaperInterface.theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; accepted-set exactness, source-shaped monotonicity/participation, and finite-or-infinite critical-value certificates imply truthfulness for nonempty nonnegative single-minded bid profiles; the domain-aware certificate only requires critical clauses on that source domain |
| Definition 10.1, greedy payment scheme | `ProofInterface.greedyNextDeniedFromOrder`, `ProofInterface.greedyPaymentFromOrder`, `PaperInterface.averageGreedyPayment`, `ProofInterface.greedy_payment_from_order_eq_zero_of_denied`, `ProofInterface.greedy_payment_from_order_eq_zero_of_no_next`, `ProofInterface.greedy_payment_from_order_eq_of_next`, `ProofInterface.averageGreedyPayment_eq_zero_of_denied`, `ProofInterface.averageGreedyPayment_eq_zero_of_no_next`, `ProofInterface.averageGreedyPayment_eq_of_next`, `ProofInterface.greedy_value_update_local_critical_window_of_sorted_erase`, `ProofInterface.averageValueUpdateWindow_sourceSortedEraseCriticalWindowOfSourceSplit`, `ProofInterface.averageSourceCriticalBranchWindowsOfAccepted` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; the full-order `n(j)` search, the concrete average-order payment rule, denied/no-next/next payment cases, suffix-window critical branches, and accepted-bid source branch windows are represented |
| Theorem 10.2, greedy allocation plus payments truthful for single-minded bidders | `PaperInterface.theorem10_2_averageGreedy_truthful`, `ProofInterface.theorem10_2_average_order_update_moves_earlier`, `ProofInterface.averageGreedyAcceptedMechanism_nonnegativeMonotonicity`, `ProofInterface.theorem10_2_greedy_truthful_of_infinity_certificate`, `ProofInterface.theorem10_2_greedy_truthful_of_nonnegative_infinity_certificate`, `ProofInterface.theorem10_2_averageGreedy_truthful_of_monotonicity`, `ProofInterface.averageGreedyNonnegativeCriticalSourceBranchData`, `ProofInterface.averageGreedyNonnegativeCriticalCertificate`, `ProofInterface.averageGreedy_acceptedPaymentCriticalOfAccepted`, `ProofInterface.greedy_accepted_mechanism_participation`, `ProofInterface.greedy_accepted_mechanism_monotonicity_of_order_moves_earlier`, `ProofInterface.theorem10_2_greedy_threshold_truthful_of_full_order_payment_certificate` | formalized | `LOS02CombinatorialAuctions/PaperInterface.lean`; `LOS02CombinatorialAuctions/ProofInterface.lean` | None; concrete average-order greedy accepted-set/payment truthfulness is proved on the source nonempty nonnegative single-minded domain; generic certificate forms remain exposed |

## Source-Audit Notes

The cached text contains Definitions 3.1--3.2, Theorem 4.1, Proposition 4.2,
Definition 5.1, Theorem 6.1, Definition 7.1, Theorem 7.2, Lemmas 9.1--9.5,
Theorem 9.6, Definition 10.1, Theorem 10.2, and the short complexity-class
note after Theorem 6.1. Current Lean coverage is the
generic combinatorial-auction interface, the generalized Vickrey auction
truthfulness and truthful-utility nonnegativity theorems, target-bundle
critical-price truthfulness and feasibility support, Theorem 6.1's
set-packing feasibility/value encoding, clique-complement, graph-edge incidence,
weighted set-packing,
threshold-decision, solver-transfer, and approximation-preserving reductions to
single-minded welfare maximization, Definition 7.1's average
amount per good, the explicit-order greedy allocation support, the Theorem 7.2
approximation endpoint for a sorted greedy order including the
source proof's rejected-bid blocker, blocking-certificate counting,
common-bid removal, and reduced-disjoint bridge, the Lemma 9.1--9.5
accepted-set utility and critical-threshold support, the finite-or-infinite
critical-value accepted-set form of Theorem 9.6 for single-minded bid profiles,
including a domain-aware certificate variant restricted to nonempty
nonnegative reports, and Definition 10.1's payment
formula from a supplied `n(j)`
next-denied function plus the full-order `n(j)` search and per-bid payment rule,
split-state/erased-blocker acceptance and fixed-order rejection lemmas for the
`n(j) = n` critical-price case, above-threshold structural acceptance from a
no-candidate prefix, value-only bid updates, Section 10 average-order algebra in
both directions, erase-stability repositioning for changed sorted orders, the
concrete deterministic average-descending order, and proofs that changing only
one bidder's value leaves that concrete order unchanged after erasing that
bidder, including the split-form fact that an original `before ++ j :: base`
order updates to an erased order `before ++ base`. The concrete average-order
greedy accepted set, allocation, and Definition 10.1 payment rule are now
exposed directly. The concrete ordered-insert suffix window removes the original
prefix and proves local acceptance of
`j` equivalent to full updated average-order greedy acceptance. The finite
accepted `n(j)=some n` branch and the accepted no-next zero-threshold branch now
bridge the local window back to the full greedy mechanism and prove equality
with the actual Definition 10.1 payment. These branches are combined into a
concrete average-order accepted-bid theorem showing that the actual greedy
payment is the critical threshold for value-only changes on the nonnegative
report domain. The average-order greedy accepted-set rule is now proved
monotone on the source nonempty nonnegative domain, and the concrete
average-order Theorem 10.2 endpoint combines that monotonicity, Participation,
the nonnegative critical-value certificate, and the source average-order
movement lemma into direct truthfulness. The
remaining source-level boundary is external computational complexity in Theorem
6.1: Lean now formalizes the clique-complement, graph-incidence, set-packing,
and single-minded welfare reductions that carry threshold decision instances
and exact and approximation solvers through the source chain, exposes
reduction-closed hardness-transfer wrappers, and exposes named abstract
`NP = ZPP` consequence wrappers. The source complexity-class note is also
represented abstractly: `P = NP` implies `NP = ZPP`, and `NP = ZPP` implies the
packaged `NP = RP`, `NP = co-RP`, and `NP = co-NP` collapse for any supplied
`RandomizedComplexityClassModel`. The current library still does not model the
machine-level semantics of NP-hardness, randomized classes, or polynomial time.

Public-release note, 2026-05-31: this folder is appropriate for public release
as a partial formalization. The remaining gap is a reusable
computational-complexity library project, not unfinished auction-specific proof
work.
