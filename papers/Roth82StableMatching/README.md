# The Economics of Matching: Stability and Incentives

## Source Version

- Paper: *The Economics of Matching: Stability and Incentives*
- Author: Alvin E. Roth
- Version checked locally: Mathematics of Operations Research, Vol. 7, No. 4 (1982)
- Official URL: https://doi.org/10.1287/moor.7.4.617
- Public PDF: https://pubsonline.informs.org/doi/epdf/10.1287/moor.7.4.617

The PDF is cached locally as `Roth82StableMatching.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache `Roth82StableMatching.txt`
is used for named-statement searches; refresh it only if the source PDF changes.

## Central Theorem Files

- `Roth82StableMatching/PaperInterface.lean`
- `Roth82StableMatching/MainTheorems.lean`
- `Roth82StableMatching/PostPaperAudit.lean`

Detailed reusable matching and deferred-acceptance primitives live in
`EconCSLib/Markets/Matching`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Paper definitions: matching utilities, stability, men/women optimality, strict marriage domain, stable procedures, truthfulness, Pareto/efficiency, profitable misreports, first-choice reports | `paper_matching_valM`, `paper_matching_valW`, `paper_is_stable`, `paper_is_men_optimal`, `paper_is_women_optimal`, `paper_strict_marriage_domain`, `paper_stable_matching_procedure`, `paper_truthful_for_men`, `paper_truthful_for_women`, `paper_is_pareto_optimal`, `paper_efficient_matching_procedure`, `paper_profitable_man_misreport`, `paper_profitable_woman_misreport`, `paper_is_strict_top_choice_for_woman`, `paper_woman_report_preserves_first_choice`, `paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain`, `paper_woman_report_misrepresents_first_choice` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; status note: formalized definitions; finite two-sided matching model. The final listed `misrepresents_first_choice` predicate is an older broad compatibility API, while `no_need_to_misrepresent_first_choice` is the source-faithful Corollary 5.1 interface. |
| Theorem 1, stable outcomes are nonempty | `paper_roth82_theorem1_stable_outcome_exists`, `paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; men-proposing DA stability is closed in `EconCSLib` via step-invariant preservation, finite-fold termination, and stability-from-terminated-invariants. On Roth's equal-size strict marriage domain, Lean also proves the DA outcome is complete. |
| Theorem 2, men- and women-optimal stable outcomes exist | `paper_da_is_men_optimal_on_strict_marriage_domain`, `paper_da_is_women_optimal_on_strict_marriage_domain`, `paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain`, plus the generic certificate wrappers `paper_roth82_theorem2_men_optimal_stable_outcome`, `paper_roth82_theorem2_women_optimal_stable_outcome`, `paper_roth82_theorem2_optimal_stable_outcomes` | formalized | `Roth82StableMatching/MainTheorems.lean`; reusable invariant in `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | None; closed on Roth's source strict marriage domain. The utility encoding uses strict scores and positive value for every potential pair to represent complete strict preferences with no outside option; the arbitrary-utility wrappers remain compatibility/certificate APIs. |
| Theorem 3, no stable procedure is strategyproof for all agents | `theorem3_stable_base_eq_x_or_y`, `theorem3_stable_woman_prime_eq_y`, `theorem3_stable_man_double_prime_eq_x`, `theorem3_counterexample_stable_behavior_of_stable_procedure`, `paper_roth82_theorem3_no_stable_truthful_procedure`, `paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; Roth's 3-by-3 profiles `P`, `P'`, `P''`, outcomes `x` and `y` are formalized. Lean proves `C(P) = {x,y}`, `C(P') = {y}`, and `C(P'') = {x}`, then derives the two-sided strategyproofness contradiction for any stable procedure on the counterexample domain. |
| Theorem 4, efficient strategyproof procedures exist | `paper_serial_dictatorship_mechanism`, `paper_roth82_theorem4_serial_dictatorship_constructed`, `paper_roth82_theorem4_serial_dictatorship_route`, `paper_roth82_theorem4_efficient_strategyproof_procedure_exists` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; the serial-dictatorship mechanism is constructed and proves efficiency, men-truthfulness, and women-truthfulness on Roth's canonical indexed strict finite marriage domain `Fin n`. The older fully generic existence wrapper remains a certificate API rather than the closed source-facing route. |
| Theorem 5, one-sided truthfulness of optimal stable procedure | `paper_da_no_profitable_strict_simple_report_on_strict_domain_of_card_eq`, `paper_da_truthful_for_men_on_strict_domain_of_card_eq`, `paper_da_truthful_for_women_on_strict_domain_of_card_eq`, `paper_roth82_theorem5_men_truthful_on_strict_domain_of_card_eq`, `paper_roth82_theorem5_women_truthful_on_strict_domain_of_card_eq`, `paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq`, plus reduction and trace helpers `paper_strict_top_report`, `paper_da_top_rejected_proposer_later_match_time`, and the older generic certificate wrappers | formalized | `Roth82StableMatching/MainTheorems.lean` | None; closed on Roth's equal-size strict marriage domain. Lean reduces arbitrary reports to strict simple reports using Lemma 1, uses Lemma 2's no-harm theorem, proves the no-new-low-proposal and unique-truthful-proposer base bridges, discharges the top-rejected-proposer later-match-time induction, and obtains the women-proposing side by role reversal. The older fully generic wrappers remain compatibility/certificate APIs outside the source-domain endpoint. |
| Corollary 5.1, opposite side has no incentive to misrepresent first choice | `paper_da_no_need_to_misrepresent_first_choice_for_women_on_strict_domain`, `paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain`, `paper_da_raise_first_choice_trace_eq_or_holds_top`, `paper_da_raise_first_choice_report_weakly_dominates`, `paper_exists_strict_top_choice_for_woman`, `paper_raise_first_choice_report_preserves_woman_first_choice`, `paper_da_true_first_choice_proposal_implies_final_true_first_choice`, `paper_da_true_first_choice_proposal_no_profitable_woman_report`, `paper_da_profitable_woman_report_implies_true_first_choice_not_proposed`, plus older compatibility wrappers `paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice` and `paper_roth82_corollary5_1_no_profitable_first_choice_misreport` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; closed for nonempty finite strict marriage markets. Lean exposes the source-faithful statement as "every report is weakly matched by some report preserving the true first choice", proves finite strict preferences have a unique first choice, raises that man above any arbitrary report, proves the bad and raised DA traces are equal until the raised trace holds the true first choice, and then uses top-choice persistence to prove weak dominance. The older no-profitable-false-top wrapper is stronger than the source reading and remains only a compatibility API. |
| Lemma 1, simple misrepresentation partner equivalence | `paper_simple_report_preserves_stability_of_partner`, `paper_roth82_lemma1_strict_simple_misrepresentation_same_partner`, plus generic wrapper `paper_roth82_lemma1_simple_misrepresentation_same_partner` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; closed for Roth's source strict marriage domain, where outcomes give the manipulator a concrete partner and the replacement report strictly ranks that partner first. The older fully generic wrapper remains a certificate API. |
| Lemma 2, successful simple misrepresentation does not hurt other men | `paper_da_simple_report_no_nonmanipulator_truthful_partner_crossing`, `paper_da_strict_simple_report_no_men_harmed_on_strict_domain`, `paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain`, plus trace bridges including `paper_da_simple_report_first_crossing_proposer_ne_manipulator`, `paper_da_removed_truthful_partner_before_active_step_yields_earlier_crossing`, and the compatibility wrapper `paper_roth82_lemma2_simple_misrepresentation_no_men_harmed` | formalized | `Roth82StableMatching/MainTheorems.lean`; proposal monotonicity, threshold-crossing, and no-rematch invariants in `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | None; closed on Roth's equal-size strict marriage domain for strict simple reports that rank the manipulator's altered DA partner uniquely first. Lean formalizes Roth's first-rejection/minimal-time induction: any worse non-manipulator yields a first crossing at his truthful partner; the crossing proposer cannot be the manipulator under the simple-report top-partner condition; the proposer's own truthful partner was removed earlier; and DA rejection invariants produce an even earlier crossing, contradiction. The older fully generic certificate wrapper remains as a compatibility API. |
| Theorem 6, men-optimal stable outcome is weakly Pareto optimal for men | `daStateAfterSteps`, `Assignment.m_complete_of_w_complete_of_card_eq`, `deferredAcceptance_complete_of_card_eq_all_pairs_acceptable`, `paper_da_last_active_step_at_time_of_complete`, `paper_da_last_active_step_at_time_implies_final_unmatched_woman_step_at_time`, `paper_da_last_unique_proposal_implies_weak_pareto_for_men`, `paper_da_complete_on_strict_marriage_domain_of_card_eq`, `paper_roth82_theorem6_on_strict_marriage_domain`, plus generic wrapper `paper_roth82_theorem6_no_feasible_outcome_strictly_better_for_all_men` | formalized | `Roth82StableMatching/MainTheorems.lean`; completeness and run-prefix support in `EconCSLib/Markets/Matching` | None; closed for Roth's nonempty equal-size strict marriage domain. Lean proves DA completeness from equal cardinality and all-pairs acceptability, derives the last active proposal step, proves Roth's final unique-proposal fact, and derives weak Pareto. |
| Theorem 7, no stable procedure prevents all `k`th-choice manipulation | `paper_rank_of_choice`, `paper_report_misrepresents_kth_choice`, `paper_stable_procedure_has_profitable_kth_choice_misreport`, `paper_no_stable_procedure_avoids_kth_choice_manipulation_on`, `PaperTheorem7ArbitraryKFamilyCertificate`, `Theorem7RankManipulationCounterexample`, `theorem7Padded_counterexample_has_profitable_rank_misreport`, `paper_roth82_theorem7_arbitrary_k_family_statement`, `paper_roth82_theorem7_arbitrary_k`, `paper_roth82_theorem7_second_choice_counterexample`, `paper_roth82_theorem7_third_choice_counterexample`, `paper_roth82_theorem7_second_or_third_choice_counterexample`, `paper_roth82_theorem7_second_or_third_choice_source_statement`, `paper_roth82_theorem7_second_or_third_choice_family_statement`, `paper_roth82_theorem7_arbitrary_k_of_family_certificate` | formalized | `Roth82StableMatching/MainTheorems.lean` | None; Lean defines the general rank-based `k`th-choice misreport predicate and proves Roth's arbitrary `k > 1` family by padding the Theorem 3 counterexample with forced dummy pairs. The padded reports move the manipulated alternative from rank `r + 2` to a different rank, stable outcomes restrict back to the original Theorem 3 core, and any stable procedure therefore yields a profitable `k`th-choice manipulation. The older `k = 2` and `k = 3` wrappers remain as compatibility witnesses. |

## Source-Audit Notes

The cached text contains Theorems 1--7, Corollary 5.1, and Lemmas 1--2. Section
2 explicitly assumes complete/transitive strict preference relations and says
only strict preferences will be considered, so the strict marriage-domain Lean
endpoints are source-domain endpoints rather than caveats. The
previous README incorrectly treated the one-sided DA truthfulness wrapper as
source Theorem 3; source Theorem 3 is the stable-strategyproofness impossibility
theorem. Current Lean coverage now closes the finite stable-set enumeration used
in Roth's Theorem 3 counterexample, proves the resulting impossibility on the
three-by-three counterexample domain, adds certificate-backed wrappers for
Theorems 4 and 6, strengthens Theorem 1 to a complete source-domain DA outcome,
closes Theorem 2 on the strict marriage domain via a reusable
DA rejected-pair invariant, constructs Roth's Theorem 4 serial-dictatorship
mechanism on strict finite marriage profiles, closes Lemma 1's strict simple-report
route from Theorem 2, closes Theorem 5's equal-size strict-domain one-sided
truthfulness theorem by combining the strict-simple-report reduction, Lemma 2,
the no-new-low-proposal bridge, and the top-rejected-proposer backward induction,
closes Theorem 6 on the nonempty equal-size strict marriage domain via DA
completeness and the final-active-step route, refines Corollary 5.1 to the
source-faithful "no need to misrepresent first choice" interface and closes the
full first-choice-preserving trace coupling,
closes Theorem 7's arbitrary `k > 1` family by padding the Theorem 3
counterexample with forced dummy pairs and a general rank-based `k`th-choice
predicate, and discharges the DA
step-preservation, finite-fold termination, and fold/invariant proof path to
stability. Overall coverage now closes every named source theorem, lemma, and
corollary in the cached paper text; older generic DA incentive certificates are
retained as compatibility APIs but are not needed for the closed source
Theorem 5 or Corollary 5.1 endpoints.
