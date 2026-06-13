# Final Validation Report: LOS02 Combinatorial Auctions

## 1. Human Verdict

- Lean formalization status: partially formalized.
- Human dashboard review status: 0/30 rows reviewed; 0 stale; 0 mismatches.
- LLM statement-translation audit: 17/30 LLM-as-judge statement rows match; 13 are uncertain; 0 stale, missing, or mismatch rows.
- Paper correctness verdict: no auction-theoretic error found.
- Qualitative proof verdict: The auction, greedy, critical-price, and single-minded truthfulness arguments are formalized in the paper-facing model. The final native complexity claims are intentionally stopped at a reusable computational-complexity boundary.
- Lean footprint: 7,288 paper-local Lean lines across 3 files; `PaperInterface.lean` has 174 lines and 30 review rows.
- Human summary: Greedy approximation, truthfulness, and Theorem 6.1 reductions are formalized. Full formalization requires computational complexity results that are out of scope.

<!-- transitive-source-premise-audit:start -->
### Transitive Source-Premise Audit

The strengthened recursive source-premise audit does not yet pass for full-status provenance. It follows paper-local wrappers and reusable-library certificate APIs, and treats certificate/source-row/external-boundary premises as full-status blockers unless they are derived internally or routed through validated paper assumptions.

Current result: the external complexity consequences, critical-value infinity axioms, and greedy-order blocking windows remain explicit partial boundaries.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

- Paper: *Truth Revelation in Approximately Efficient Combinatorial Auctions*
- Authors: Daniel Lehmann, Liadan Ita O'Callaghan, and Yoav Shoham
- Source version: Journal of the ACM 49(5), 2002
- Lean folder: `LOS02CombinatorialAuctions/`
- Human-facing theorem file: `LOS02CombinatorialAuctions/PaperInterface.lean`
- DAG artifacts: `LOS02CombinatorialAuctions/DependencyDAG.tex`, `LOS02CombinatorialAuctions/DependencyDAG.pdf`
- Supporting audit ledger: `LOS02CombinatorialAuctions/POST_FORMALIZATION_AUDIT.md`

## 3. What Has Been Proven

The formalization closes the finite combinatorial-auction core used by the paper: utility and truthfulness predicates, generalized Vickrey auction truthfulness and nonnegative truthful utility, the single-minded welfare/set-packing encodings, the greedy square-root approximation, the critical-value lemmas, and the average-greedy mechanism truthfulness theorem.

The theorem endpoints involving native computational complexity are intentionally partial. Lean exposes exact and approximation-preserving solver consequences through abstract class and external-consequence interfaces, but it does not yet contain a reusable machine-level theory of polynomial-time reductions, NP-hardness/inapproximability, ZPP, or the cited clique/set-packing hardness facts.

## 4. Paper Assumption Provenance And Boundary Ledger

> Strict premise-source audit update (2026-06-12): `assumption_match_llm.json` now records per-premise judgments for this paper's `Assumptions.lean` ledger. Current result: 6/8 premises are source-matched to the local JACM text and 2/8 remain visible partial-formalization boundaries. The remaining boundaries are exactly the external Theorem 6.1 complexity facts: native NP-hardness/inapproximability and the machine-level `NP = ZPP` consequence.

Every paper-facing premise is now routed through
`LOS02CombinatorialAuctions/Assumptions.lean` and checked by
`assumption_match_llm.json`. The auction-theoretic premises below are source
conditions; the Theorem 6.1 complexity rows are documented partial-formalization
boundaries.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_admissible_combinatorial_report_domain` | source-matched paper condition | Definition 3.2 truthfulness is stated over true bidder types and declaration vectors. |
| `assumption_theorem7_optimal_allocation_feasible` | source-matched paper condition | Theorem 7.2 compares greedy with `OP`, the optimal feasible allocation. |
| `assumption_theorem7_optimal_bidders_in_order` | source-matched paper condition | Theorem 7.2 processes the sorted bid list containing the optimal bids under comparison. |
| `assumption_lemma9_denied_bidder_case` | source-matched paper condition | Lemma 9.2 is exactly the denied-bidder case. |
| `assumption_lemma9_nonnegative_value_deviation` | source-matched paper condition | Single-minded value deviations stay in the nonnegative source declaration domain. |
| `assumption_lemma9_finite_large_threshold` | source-matched paper condition | Lemma 9.5 handles the finite critical-price comparison for the larger desired set. |
| `assumption_external_exact_set_packing_complexity_boundary` | partial boundary | External Karp/Hastad-style hardness and polynomial-time transfer facts. |
| `assumption_external_approximation_set_packing_complexity_boundary` | partial boundary | External inapproximability and randomized-complexity consequence facts. |

Additional assumptions beyond the paper: none for the auction, greedy,
critical-price, or single-minded-truthfulness portions. The final Theorem 6.1
machine-level NP-hardness and `NP = ZPP` consequences remain partial because
the repository does not yet contain reusable machine-level complexity-class and
hardness infrastructure.

## 5. Proof-Strategy Deviations

- The source complexity claims are represented by abstract consequence
  interfaces rather than a native computational model.
- The auction-mechanism portions otherwise follow the paper's finite
  combinatorial-auction and single-minded-bidder proof structure.

## 6. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 7. Library Lift Pass

None separately recorded in the existing report.

## 8. DAG Audit

No separate DAG audit note is recorded in the existing report.

## 9. Conditional Results and Remaining Gaps

No paper-facing auction, greedy approximation, critical-price, or
single-minded-truthfulness endpoint is left open in the current model. The
remaining gap is reusable library infrastructure: polynomial-time many-one
reductions, NP-hardness/inapproximability facts for the cited clique/set-packing
route, randomized classes such as ZPP, and the machine-level meaning of
polynomial-time algorithms.

## 10. Suspected Paper Errors or Inconsistencies

- None found.

## 11. Validation Checks

Recent checks built the LOS02 paper target, the reusable complexity-class
module, the full `EconCSLib` target, and the dependency DAG. The repository
audit records the LOS02 dashboard surface as informational; unrelated warnings
remain elsewhere in the private repository.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 30 rows; 17 match, 13 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

Flagged rows:
- `utility`: uncertain. The draft is mostly a Lean function signature and does not state the utility formula in paper language.
- `truthfulOn`: uncertain. The draft is mostly a Lean predicate signature and does not state the truthfulness condition in paper language.
- `generalizedVickreyAuction`: uncertain. The draft is mostly a Lean function signature and does not state the generalized Vickrey allocation/payment rule in paper language.
- `singleMindedAcceptedMechanism`: uncertain. The draft is mostly a Lean function signature and does not state the accepted-bid mechanism in paper language.
- `singleMindedTruthfulOn`: uncertain. The draft is mostly a Lean predicate signature and does not state the single-minded truthfulness condition in paper language.
- `nonnegativeNonemptySingleMindedProfile`: uncertain. The draft is mostly a Lean predicate signature and does not spell out the nonnegative/nonempty profile condition.
- `weightedSetPackingValue`: uncertain. The draft is mostly a Lean function signature and does not state the weighted set-packing objective formula.
- `setPackingSingleMindedBids`: uncertain. The draft is mostly a Lean function signature and does not state the set-packing construction from bids.
- `averageAmountPerGood`: uncertain. The draft is mostly a Lean function signature and does not state the average-demand quantity in paper language.
- `averageOrderOf`: uncertain. The draft is mostly a Lean function signature and does not state the average ordering rule in paper language.
- `greedyAcceptedFromOrder`: uncertain. The draft is mostly a Lean function signature and does not state the greedy acceptance rule in paper language.
- `averageGreedyAcceptedSet`: uncertain. The draft is mostly a Lean function signature and does not state the average-greedy accepted set in paper language.
- `averageGreedyPayment`: uncertain. The draft is mostly a Lean function signature and does not state the payment formula in paper language.

## 12. Final Verdict

LOS02 is suitable as a public partial formalization. The EconCS auction and
truthfulness content is formalized in the current model, while the final
machine-level complexity conclusions remain conditional on reusable complexity
infrastructure that is not yet in the library.

- Completion status: partially formalized.
- Summary: Greedy approximation, truthfulness, and Theorem 6.1 reductions are formalized. Full formalization requires computational complexity results that are out of scope.

## 13. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| abbrev utility | `utility` | uncertain. The draft is mostly a Lean function signature and does not state the utility formula in paper language. |
| abbrev truthfulOn | `truthfulOn` | uncertain. The draft is mostly a Lean predicate signature and does not state the truthfulness condition in paper language. |
| abbrev generalizedVickreyAuction | `generalizedVickreyAuction` | uncertain. The draft is mostly a Lean function signature and does not state the generalized Vickrey allocation/payment rule in paper language. |
| abbrev singleMindedAcceptedMechanism | `singleMindedAcceptedMechanism` | uncertain. The draft is mostly a Lean function signature and does not state the accepted-bid mechanism in paper language. |
| abbrev singleMindedTruthfulOn | `singleMindedTruthfulOn` | uncertain. The draft is mostly a Lean predicate signature and does not state the single-minded truthfulness condition in paper language. |
| abbrev nonnegativeNonemptySingleMindedProfile | `nonnegativeNonemptySingleMindedProfile` | uncertain. The draft is mostly a Lean predicate signature and does not spell out the nonnegative/nonempty profile condition. |
| abbrev weightedSetPackingValue | `weightedSetPackingValue` | uncertain. The draft is mostly a Lean function signature and does not state the weighted set-packing objective formula. |
| abbrev setPackingSingleMindedBids | `setPackingSingleMindedBids` | uncertain. The draft is mostly a Lean function signature and does not state the set-packing construction from bids. |
| abbrev averageAmountPerGood | `averageAmountPerGood` | uncertain. The draft is mostly a Lean function signature and does not state the average-demand quantity in paper language. |
| abbrev averageOrderOf | `averageOrderOf` | uncertain. The draft is mostly a Lean function signature and does not state the average ordering rule in paper language. |
| abbrev greedyAcceptedFromOrder | `greedyAcceptedFromOrder` | uncertain. The draft is mostly a Lean function signature and does not state the greedy acceptance rule in paper language. |
| abbrev averageGreedyAcceptedSet | `averageGreedyAcceptedSet` | uncertain. The draft is mostly a Lean function signature and does not state the average-greedy accepted set in paper language. |
| abbrev averageGreedyPayment | `averageGreedyPayment` | uncertain. The draft is mostly a Lean function signature and does not state the payment formula in paper language. |
| abbrev theorem4_1_generalized_vickrey_truthful | `theorem4_1_generalized_vickrey_truthful` | - Theorem 4.1: generalized Vickrey auctions are truthful. |
| abbrev proposition4_2_generalized_vickrey_truthful_utility_nonneg | `proposition4_2_generalized_vickrey_truthful_utility_nonneg` | - Proposition 4.2: truthful GVA bidder utility is nonnegative. |
| abbrev theorem6_1_set_packing_feasibility_encoding_correct | `theorem6_1_set_packing_feasibility_encoding_correct` | - Theorem 6.1 set-packing feasibility encoding. |
| abbrev theorem6_1_set_packing_value_encoding_correct | `theorem6_1_set_packing_value_encoding_correct` | - Theorem 6.1 set-packing value encoding. |
| abbrev theorem6_1_weighted_set_packing_reduction | `theorem6_1_weighted_set_packing_reduction` | - Theorem 6.1 weighted set-packing reduction. |
| abbrev theorem6_1_clique_decision_single_minded_welfare_reduction | `theorem6_1_clique_decision_single_minded_welfare_reduction` | - Theorem 6.1 clique-to-single-minded welfare reduction. |
| abbrev theorem6_1_external_optimal_solver_np_eq_zpp | `theorem6_1_external_optimal_solver_np_eq_zpp` | - Theorem 6.1 external exact-solver complexity consequence. |
| abbrev theorem6_1_external_approximation_solver_np_eq_zpp | `theorem6_1_external_approximation_solver_np_eq_zpp` | - Theorem 6.1 external approximation-solver complexity consequence. |
| abbrev complexity_note_np_eq_zpp_implies_randomized_collapse | `complexity_note_np_eq_zpp_implies_randomized_collapse` | - Complexity-class note: `NP = ZPP` implies the randomized collapse. |
| abbrev theorem7_2_sqrt_norm_approx_of_sorted_order | `theorem7_2_sqrt_norm_approx_of_sorted_order` | - Theorem 7.2 greedy allocation square-root approximation. |
| abbrev lemma9_1_exists_nonnegative_critical_value_of_monotonicity | `lemma9_1_exists_nonnegative_critical_value_of_monotonicity` | - Lemma 9.1 critical-value existence from monotonicity. |
| abbrev lemma9_2_denied_bidder_utility_eq_zero | `lemma9_2_denied_bidder_utility_eq_zero` | - Lemma 9.2 denied-bidder utility is zero. |
| abbrev lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate | `lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate` | - Lemma 9.3 truth-telling utility is nonnegative under critical-value certificates. |
| abbrev lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms | `lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms` | - Lemma 9.4 no profitable value-only lie under nonnegative infinity axioms. |
| abbrev lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate | `lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate` | - Lemma 9.5 finite threshold monotonicity. |
| abbrev theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms | `theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms` | - Theorem 9.6 critical axioms imply truthfulness for single-minded bidders. |
| abbrev theorem10_2_averageGreedy_truthful | `theorem10_2_averageGreedy_truthful` | - Theorem 10.2 average-order greedy mechanism truthfulness. |
<!-- lean-derived-definitions:end -->

## 14. Named Theorem Statements Checked

### Theorem-by-Theorem Validation

| Paper item | Status | Statement match | Notes |
|---|---|---|---|
| Definitions 3.1--3.2, direct combinatorial-auction mechanism and truthfulness | formalized | exact finite model | Uses finite bidder/item combinatorial auctions. |
| Theorem 4.1, generalized Vickrey auction is truthful | formalized | exact | Represented by a welfare-maximizing allocation certificate and Clarke-pivot payments. |
| Proposition 4.2, truthful GVA utility nonnegative | formalized | exact | Uses the paper's nonnegative bundle-value domain. |
| Definition 5.1, single-minded bidders | formalized | exact finite model | Nonempty single-minded profiles are explicit. |
| Theorem 6.1, set-packing and single-minded welfare reductions | formalized | exact for finite reductions | Includes feasibility/value encodings, clique/complement/independent-set/set-packing routes, and exact/approximation-preserving solver transfers. |
| Theorem 6.1, native NP-hardness and `NP = ZPP` consequences | partially formalized | conditional | Exposed through abstract external-consequence and class-model wrappers because the library does not yet formalize native machine-level complexity classes. |
| Complexity-class note after Theorem 6.1 | partially formalized | abstract class model | Lean proves the collapse implications from supplied class-relationship fields, not from a machine model. |
| Definition 7.1, average amount per good and greedy order | formalized | exact finite model | Includes the deterministic average-descending order used by the greedy mechanism. |
| Theorem 7.2, greedy allocation approximation | formalized | exact finite model | Includes blocker extraction, blocking-certificate counting, common-bid removal, and reduced-disjoint reasoning. |
| Lemmas 9.1--9.5, critical values and utility/payment facts | formalized | exact source domain | Covers nonempty nonnegative single-minded bid profiles and finite-or-infinite critical-value certificates. |
| Theorem 9.6, critical axioms imply truthfulness | formalized | exact source domain | Exactness, monotonicity, participation, and critical-value certificates imply truthfulness. |
| Definition 10.1, greedy payment scheme | formalized | exact finite model | Represents denied/no-next/next payment cases and accepted-bid criticality. |
| Theorem 10.2, average-order greedy mechanism truthfulness | formalized | exact source domain | Concrete allocation and payment rule are truthful on nonempty nonnegative single-minded profiles. |

## 15. Paper-Facing Statement Validator Ledger

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| abbrev averageAmountPerGood | `averageAmountPerGood` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the average-demand quantity in paper language. |
| abbrev averageGreedyAcceptedSet | `averageGreedyAcceptedSet` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the average-greedy accepted set in paper language. |
| abbrev averageGreedyPayment | `averageGreedyPayment` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the payment formula in paper language. |
| abbrev averageOrderOf | `averageOrderOf` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the average ordering rule in paper language. |
| abbrev complexity_note_np_eq_zpp_implies_randomized_collapse | `complexity_note_np_eq_zpp_implies_randomized_collapse` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev generalizedVickreyAuction | `generalizedVickreyAuction` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the generalized Vickrey allocation/payment rule in paper language. |
| abbrev greedyAcceptedFromOrder | `greedyAcceptedFromOrder` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the greedy acceptance rule in paper language. |
| abbrev lemma9_1_exists_nonnegative_critical_value_of_monotonicity | `lemma9_1_exists_nonnegative_critical_value_of_monotonicity` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma9_2_denied_bidder_utility_eq_zero | `lemma9_2_denied_bidder_utility_eq_zero` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate | `lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms | `lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate | `lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev nonnegativeNonemptySingleMindedProfile | `nonnegativeNonemptySingleMindedProfile` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean predicate signature and does not spell out the nonnegative/nonempty profile condition. |
| abbrev proposition4_2_generalized_vickrey_truthful_utility_nonneg | `proposition4_2_generalized_vickrey_truthful_utility_nonneg` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev setPackingSingleMindedBids | `setPackingSingleMindedBids` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the set-packing construction from bids. |
| abbrev singleMindedAcceptedMechanism | `singleMindedAcceptedMechanism` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the accepted-bid mechanism in paper language. |
| abbrev singleMindedTruthfulOn | `singleMindedTruthfulOn` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean predicate signature and does not state the single-minded truthfulness condition in paper language. |
| abbrev theorem10_2_averageGreedy_truthful | `theorem10_2_averageGreedy_truthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem4_1_generalized_vickrey_truthful | `theorem4_1_generalized_vickrey_truthful` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem6_1_clique_decision_single_minded_welfare_reduction | `theorem6_1_clique_decision_single_minded_welfare_reduction` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem6_1_external_approximation_solver_np_eq_zpp | `theorem6_1_external_approximation_solver_np_eq_zpp` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem6_1_external_optimal_solver_np_eq_zpp | `theorem6_1_external_optimal_solver_np_eq_zpp` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem6_1_set_packing_feasibility_encoding_correct | `theorem6_1_set_packing_feasibility_encoding_correct` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem6_1_set_packing_value_encoding_correct | `theorem6_1_set_packing_value_encoding_correct` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem6_1_weighted_set_packing_reduction | `theorem6_1_weighted_set_packing_reduction` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem7_2_sqrt_norm_approx_of_sorted_order | `theorem7_2_sqrt_norm_approx_of_sorted_order` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms | `theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms` | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:45Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| abbrev truthfulOn | `truthfulOn` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean predicate signature and does not state the truthfulness condition in paper language. |
| abbrev utility | `utility` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the utility formula in paper language. |
| abbrev weightedSetPackingValue | `weightedSetPackingValue` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:45Z): The draft is mostly a Lean function signature and does not state the weighted set-packing objective formula. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.
