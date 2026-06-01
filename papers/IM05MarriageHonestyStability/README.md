# Marriage, Honesty, and Stability

## Source Version

- Paper: *Marriage, Honesty, and Stability*
- Authors: Nicole Immorlica and Mohammad Mahdian
- Version checked locally: MIT Laboratory for Computer Science technical report
  MIT-LCS-TR-913, PDF created April 11, 2005; also published in SODA 2005
- Source URL: https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TR-913.pdf
- Microsoft Research page: https://www.microsoft.com/en-us/research/publication/marriage-honesty-and-stability/

The source PDF is cached locally as `IM05MarriageHonestyStability.pdf` and
ignored by the paper-folder `.gitignore`. The extracted text cache
`IM05MarriageHonestyStability.txt` is usable for source audits.

## Central Theorem File

- `IM05MarriageHonestyStability/MainTheorems.lean`
- `IM05MarriageHonestyStability/ProofStrategy.md` records the live outside-Lean
  proof plan for the remaining named seams.

Reusable matching infrastructure lives in `EconCSLib/Markets/Matching`; reusable
finite/asymptotic probability support belongs in `EconCSLib/Foundations`.

## Named-Result Inventory

Text-cache lines for named results:

- Theorem A, line 115: men-proposing DA is stable and men-optimal / women-pessimal.
- Theorem B, line 128: men-proposing DA output is independent of proposal order.
- Theorem C, line 136: the set of single agents is the same in all stable matchings.
- Theorem D, line 162: side-proposing DA is truthful for the proposing side.
- Conjecture 1, line 122: Roth-Peranson `c_k(n)/n -> 0`.
- Theorem 3.1, line 154: arbitrary women preferences and arbitrary fixed draw distribution `D`.
- Theorem 3.2, line 173: uniform-list constant bound `e^(k+1) + k^2`.
- Corollary 3.1, line 188: truthful best response with high probability.
- Corollary 3.2, line 216: complete-information equilibrium with `1 - o(1)` truthful strategies in expectation.
- Corollary 3.3, line 185: approximate Bayesian-Nash equilibrium under women-optimal DA.
- Algorithm 4.1, line 228 and Theorem 4.1, line 273: count stable husbands in one proposal run.
- Algorithm 4.2, line 260: deferred-decisions random-list simulation.
- Lemma 4.1, line 317: bound on `E[1/(X_mu(g)+1)]`.
- Lemma 4.2, line 363: `X_mu(g) >= Y_g`.
- Lemma 4.3, line 375: lower bound on expected number of single popular women.
- Lemma 4.4, line 428: variance of `Y_g` is at most its expectation.
- Lemma 6.1, line 496: uniform-list reciprocal-singles bound.
- Lemma 6.2, line 518: reduction to occupancy empty-bin count.
- Lemma 6.3, line 605: empty-bin reciprocal expectation bound.
- Appendix Lemma A.1, line 747: lower bound on a fixed man's single probability.
- Appendix Lemma A.2, line 770: monotonicity of single probability in number of men.

## DAG Status Refresh

The dependency DAG was refreshed against this named-result inventory on
May 16, 2026.  Its topology intentionally remains the initial paper-roadmap
topology: source-named definitions, algorithms, lemmas, theorems, corollaries,
and appendix lemmas stay as the primary nodes, while proof-helper families and
certificate packages stay in this README and the proof notes.

The main reason the DAG still has several non-green nodes is not stale proof
work, but paper-level obligations that are genuinely still conditional:
Theorem 4.1 is reduced to
`im05_Algorithm41SourcePairWitnessCompletionCertificate`; Theorem 3.1 still
needs Theorem 4.1, concrete Algorithm 4.2 stable-market wiring, and the
repaired Lemma 4.4 tail-variance input; Theorem 3.2 still needs the concrete
Section 6 experiment construction and the remaining Experiment 3 per-pair
probability reduction.  Lemma 4.4 is marked as a caveat rather than open
because the printed unrestricted variance statement is false for arbitrary
nonuniform `D^k`, and the Lean development records counterexamples plus the
corrected tail-count bridge.

As of the May 16, 2026 pause handoff, IM05 should not be treated as nearly
finished.  The right next work is a focused proof campaign on one of three
remaining seams: the Algorithm 4.1 pair-witness completion certificate, the
repaired Lemma 4.4 tail-variance input for Theorem 3.1, or the concrete
Section 6 experiment construction for Theorem 3.2.  `NEXT_AGENT_HANDOFF.md`
records these as stronger-model pickup targets.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Stable matching and stable-partner counting definitions | `im05_stable_matching`, `im05_stableHusbands`, `im05_stableWives`, `im05_hasMoreThanOneStableHusband`, `im05_hasMoreThanOneStableHusband_iff_exists_distinct`, `im05_hasMoreThanOneStableWife_iff_exists_distinct`, `im05_not_multiStableHusband_eq_of_stable_matches`, `im05_not_multiStableWife_eq_of_stable_matches`, `im05_stableHusbands_relabelWomen`, `im05_hasMoreThanOneStableHusband_relabelWomen`, `paper_im05_hasMoreThanOneStableHusband_of_woman_relabeling`, `Assignment.relabelWomen`, `isStable_relabelWomen_iff`, `im05_multiStableHusbandCount`, `im05_multiStableWifeCount`, `im05_singleMen`, `im05_singleWomen`, `im05_strict_marriage_domain`, `im05_women_deferredAcceptance`, `womenDeferredAcceptance` | formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Markets/Matching/Basic.lean`; `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | None; uses the repository's optional-partner stable matching API, where unmatched value is `0`; the complete strict marriage domain and women-proposing role reversal are exposed locally for paper-facing wrappers, with the role reversal now backed by a library primitive. The multi-stable-partner predicates now have explicit two-stable-matching witness forms for later probability events and symmetric count definitions for women-with-many-stable-husbands and men-with-many-stable-wives. If an agent is not multi-stable, any two stable matchings that match that agent give the same partner. Woman-side market relabeling is now a reusable matching-library primitive, and the fixed-woman multi-stable event is proved invariant under that relabeling. |
| Theorem A, side-proposing stability/optimality/pessimality | `paper_im05_theoremA_men_proposing_finds_stable`, `paper_im05_theoremA_men_proposing_men_optimal`, `paper_im05_theoremA_men_proposing_women_pessimal`, `paper_im05_theoremA_women_proposing_finds_stable`, `paper_im05_theoremA_women_proposing_women_optimal`, `paper_im05_theoremA_women_proposing_men_pessimal`, `da_is_women_pessimal_of_strict_preferences`, `womenDeferredAcceptance_is_women_optimal_of_strict_preferences`, `womenDeferredAcceptance_is_men_pessimal_of_strict_preferences` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | Stability is unconditional for both side-proposing DA procedures. Optimality and opposite-side pessimality are closed for the strict all-acceptable marriage domain, with equal cardinality explicit for the pessimality/completeness steps. The full optional-list version is still not separated from the complete-domain wrapper. |
| Theorem B | `paper_im05_theoremB_unique_men_optimal_stable_matching`, `paper_im05_theoremB_any_men_optimal_output_eq_deferredAcceptance`, `men_optimal_stable_matching_unique_of_card_eq_all_pairs_acceptable` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | Formalizes the source derivation that the men-optimal stable matching is unique, so any stable men-optimal algorithm output equals the canonical men-proposing DA output. The remaining caveat is that the repository still does not expose a separate arbitrary proposal-order DA trace whose output is proved men-optimal. |
| Theorem C | `paper_im05_theoremC_same_singles_on_complete_domain`; `stable_complete_of_card_eq_all_pairs_acceptable` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | Closed for the equal-size all-acceptable marriage-domain special case: every stable matching is complete, so the single-agent sets are both empty. The full optional-domain same-singles/rural-hospitals theorem remains open. |
| Theorem D | `paper_im05_theoremD_optimal_side_truthful_on_strict_domain_of_card_eq`; reuses `Roth82StableMatching.paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `Roth82StableMatching/MainTheorems.lean` | Closed as a thin IM05 wrapper around the verified Roth Theorem 5 result for the equal-size strict complete marriage domain. It does not yet state a separate short-list/incomplete-domain truthfulness theorem. |
| Conjecture 1 / Theorem 3.1 | `paper_im05_expected_multiStableHusbandCount_le_sum_bounds`, `paper_im05_expected_multiStableHusbandCount_le_exceptional_add_tail_bounds`, `paper_im05_theorem3_1_tail_term_bound`, `paper_im05_theorem3_1_tail_sum_bound`, `paper_im05_theorem3_1_count_bound_from_tail_probabilities`, `paper_im05_ck_linearity_expected_multiStableHusbandCount`, `paper_im05_theorem3_1_log_sqrt_ratio_bound_implies_fraction_vanishes`, `paper_im05_theorem3_1_log_sqrt_count_bound_implies_fraction_vanishes`, `tendsto_const_div_log_nat_nhds_zero`, `tendsto_log_div_sqrt_nat_nhds_zero` | partially formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Math/Asymptotics.lean` | The finite summation skeleton and final asymptotic endpoint of the proof are formalized: expected multi-stable-husband count equals the sum of fixed-woman probabilities, pointwise bounds sum to an expected-count bound, exceptional women can be charged trivially while tail bounds are summed separately, the paper's exponential tail term sums to `3 sqrt(n) log(n)/(4k)` past the `16nk/log n` threshold, the displayed finite count bound follows from pointwise tail probabilities, Lemma 4.1's variance/Chebyshev-to-reciprocal bridge and final algebra endpoint are formalized, Lemma 4.4's variance conclusion is formalized from pairwise negative correlation, and the paper's `16nk/log n + 3 sqrt(n) log n/(4k)` count bound implies `c_k(n)/n -> 0`. The full theorem still requires Algorithm 4.2's deferred-decisions probability space, Theorem 4.1, and the paper-specific probability construction supplying Lemmas 4.2-4.4. The published Lemma 4.4 route has a validation issue for nonuniform `D`: the arbitrary-`k` one-man negative-correlation claim is false at `k = 3`. |
| Theorem 3.1 linearity proof line | `paper_im05_ck_linearity_expected_multiStableHusbandCount`, `paper_im05_linearity_expected_multiStableWifeCount`, `pmfExp_card_filter_eq_sum_pmfProb` | formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | None; formalizes the source line `c_k(n) = sum_g Pr[g has more than one stable husband]` and its symmetric stable-wife count analogue as the generic finite identity that the expected count of an outcome-dependent finite set equals the sum of its elementwise event probabilities. |
| Theorem 3.2 algebraic endpoint | `paper_im05_theorem3_2_from_lemma6_1`, `paper_im05_theorem3_2_from_lemma6_2`, `paper_im05_theorem3_2_from_draw_usedBins_experiments_of_four_le` | conditional | `IM05MarriageHonestyStability/MainTheorems.lean` | Proves the paper's `c_k(n) <= e^(k+1)+k^2` endpoint from the source reduction `c_k(n) <= n E[1/(X+1)]` and either Lemma 6.1, Lemma 6.2/Lemma 6.3, or the combined five-experiment draw-prefix route. The Algorithm 4.1/4.2 reduction and Experiment 3 per-pair probability proof remain open. |
| Theorem 3.2 implication to vanishing fraction | `paper_im05_theorem3_2_bound_implies_fraction_vanishes` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Math/Asymptotics.lean` | Proves the asymptotic bridge from the paper's constant bound to `c_k(n)/n -> 0`; the probabilistic proof of the bound itself remains open. |
| Corollaries 3.1-3.3 | `paper_im05_theorem3_2_fixed_woman_probability_bound_of_symmetry`, `paper_im05_fixed_woman_probability_symmetry_of_uniform_relabeling`, `paper_im05_theorem3_2_fixed_woman_probability_bound_of_uniform_relabeling`, `paper_im05_hasMoreThanOneStableHusband_of_woman_relabeling`, `paper_im05_theorem3_2_fixed_woman_probability_bound_of_uniform_sample_woman_relabeling`, `paper_im05_theorem3_2_fixed_woman_probability_bound_of_uniform_function_sample_woman_relabeling`, `paper_im05_theorem3_2_fixed_woman_probability_bound_of_uniform_injective_function_sample_woman_relabeling`, `im05_not_multiStableHusband_eq_of_stable_matches`, `im05_not_multiStableWife_eq_of_stable_matches`, `paper_im05_corollary3_1_probability_bound_implies_o_one`, `pmfProb_uniformPMF_equiv`, `pmfProb_uniformPMF_eq_of_comp_equiv`, `pmfProb_uniformPMF_fun_range_relabel`, `pmfProb_uniformPMF_injective_fun_range_relabel`, `TendsToZero_of_nonneg_le_const_div` | partially formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Markets/Matching/Basic.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Math/Asymptotics.lean` | Formalizes the finite symmetry bridge used by the uniform-distribution corollary and the asymptotic endpoint: a constant bound on the expected number of multi-stable-husband women implies an `O(1/n)` bound for any fixed woman under event-probability symmetry, and any nonnegative sequence with that bound is `o(1)`. The symmetry hypothesis now has both components needed by the random-list model plus a combined wrapper: provide a uniform sample-space equivalence, a woman permutation sending the target woman to the compared woman, and pointwise valuation-relabeling equalities. Uniform finite-function samples, including with-replacement draw-prefix spaces, and ordered without-replacement injective-function samples now both have specialized pointwise woman-relabeling wrappers. The deterministic unique-partner core is closed for stable matchings that match the agent; a full best-response wrapper still needs the mechanism/incentive comparison hypotheses. |
| Algorithm 4.1 / Theorem 4.1 | `im05_worstToBestForWoman`, `im05_algorithm41TargetAccepts`, `im05_algorithm41TargetStandardAfterAccept`, `im05_algorithm41TargetStandard_value_mono_of_accepts`, `im05_algorithm41HasProposedTo`, `im05_algorithm41HistoryAccepts`, `im05_algorithm41BestProposedSoFar`, `im05_algorithm41SourceStep`, `im05_algorithm41SourceStepDivorceTarget`, `im05_algorithm41SourceStepTargetAccepted`, `im05_algorithm41SourceDivorceTargetStateAfterSteps`, `im05_algorithm41SourceDivorceTargetFinalState`, `im05_algorithm41SourceDivorceTargetAcceptedMen`, `im05_algorithm41SourceStep_eq_daStep_of_invariants`, `im05_algorithm41SourceStep_eq_daStep_of_invariantsExceptWoman_nonTarget`, `im05_deferredAcceptanceState_currentMatchOrder_of_allPairsAcceptable`, `im05_algorithm41DivorcedState_currentMatchOrder_of_allPairsAcceptable`, `im05_algorithm41SourceDivorceTargetStateAfterSteps_currentMatchOrder_of_allPairsAcceptable`, `im05_algorithm41SourceDivorceTargetFinalState_terminated`, `im05_algorithm41SourceStepDivorceTarget_preserves_invariantsExceptWoman_of_allPairsAcceptable`, `im05_algorithm41SourceDivorceTargetFinalState_stable_except_target_of_allPairsAcceptable`, `im05_algorithm41SourceDivorceTargetFinalState_w_match_target_none`, `im05_algorithm41SourceDivorceTargetStateAfterSteps_m_proposals_subset_of_le`, `im05_algorithm41SourceStepTargetAccepted_ne_of_lt`, `im05_algorithm41InitialHusband_ne_sourceStepTargetAccepted`, `im05_algorithm41SourceDivorceTargetAcceptedMen_nodup`, `im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest`, `im05_algorithm41SourceDivorceTargetAcceptedMen_forward_of_allPairsAcceptable`, `paper_im05_theorem4_1_base_case_worst_stable_husband`, `im05_algorithm41SourceStep_target_reject_not_mem_stableHusbands_of_rejected_pair_impossible_except_target`, `im05_stableHusband_target_proposal_mem_sourceDivorceTargetAcceptedMen_of_trace_rejected_package_of_allPairsAcceptable`, `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_trace_target_proposals`, `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_target_chosen_prefix`, `im05_SourceStepNonTargetRejectedPairExclusions`, `im05_SourceStepNonTargetRejectedPairExclusions_of_full_rejectedPairImpossible`, `im05_algorithm41SourceStepDivorceTarget_preserves_rejectedPairImpossibleExceptWoman_of_stepNonTargetExclusions`, `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepNonTargetExclusions_prefix`, `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_allPairsAcceptable_card_le`, `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals`, `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`, `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_card_lower`, `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_backward`, `paper_im05_theorem4_1_outputs_exactly_stable_husbands_of_algorithm41_certificate`, `paper_im05_theorem4_1_ordered_stable_husband_list_exists`, plus the older `im05_algorithm41HeldMen` / `im05_algorithm41SourceHeldMen` scaffold declarations | conditional | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | The paper-facing output contract is formalized: a certified Algorithm 4.1 output contains exactly the stable husbands of the target woman, has the stable-husband cardinality, and is ordered from her worst stable husband to her best. The corrected target-divorcing trace now records target acceptance events, immediately divorces `g`, preserves target-exception invariants on all-acceptable domains, terminates at the finite proposal bound, keeps `g` unmatched after every corrected prefix, and has monotone shrinking proposal histories. Its accepted-men event list is proved nodup and ordered worst-to-best; the initial DA husband is proved to be the worst stable husband on the strict equal-size all-acceptable domain, and later accepted target events are proved stable husbands under all-acceptable preferences. Source-step acceptance is now equivalent to ordinary DA under full invariants and away from the target under target-exception invariants, which closes current-match-order automatically from the initial DA state through every corrected prefix. The strongest current one-stop endpoint is `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`; the exact remaining certificate is `im05_Algorithm41SourcePairWitnessCompletionCertificate`, which packages the non-target blocking-pair witness preference obligation and the final target-removal obligation. The older non-divorcing source-held-men trace is retained only as scaffold and blocking-pair proof infrastructure. |

Algorithm 4.1 witness update: target-acceptance events and corrected
accepted-men outputs now have witness-form variants,
`im05_algorithm41SourceStepTargetAccepted_stable_match_witness_of_allPairsAcceptable`
and
`im05_algorithm41SourceDivorceTargetAcceptedMen_stable_match_witness_of_allPairsAcceptable`,
returning an explicit stable matching with `m_match m = some g`.

Algorithm 4.1 update: the per-step non-target exclusion predicate is now
reduced to exception-partner side conditions for the prior/chosen blocking
proposer; see
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_exception_partner_exclusions_prefix`.
The compact prefix predicate is `im05_SourceTraceExceptionPartnerExclusions`,
and the corresponding final conditional wrapper is
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceExceptionPartnerExclusions`.
This now has a stable-husband-set reduction:
`im05_SourceStepNonTargetBlockersNotStableHusbands` lifts to
`im05_SourceTraceNonTargetBlockersNotStableHusbands` via
`im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers`, which
implies the compact exception-partner predicate via
`im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`,
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_nonTargetBlockersNotStableHusbands`
packages that reduction at the paper-facing output-contract level.  The direct
step-local paper-facing wrapper is
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.
The source-faithful target-proposal coverage condition now excludes the initial
DA husband, which is already output before the continued-proposal loop:
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`,
`im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_trace_target_proposals_except_initial`,
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial`, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`.
Coverage can now be proved from final proposal-set removal:
`im05_algorithm41SourceStepDivorceTarget_removed_proposal_eq_chosen`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps_removed_proposal_exists_chosen`,
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_removed_target_proposals`,
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.
The start side of this removed-proposals condition is now closed on the strict
equal-size all-acceptable domain by
`im05_noninitial_stableHusband_mem_divorced_proposals`, leaving only final
removal of `g` from each non-initial stable husband's proposal set in
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands`.
Final removal is itself reduced by
`im05_not_mem_proposals_of_terminated_prefers_target_to_current` and
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_prefers_target_to_current`
to a final-match preference condition, packaged in
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands`.
The final-removal and final-preference endpoints also have equal-size wrappers
ending in `_of_card_eq`, so the explicit initial-husband witness is no longer
needed at these intermediate paper-facing layers.
The same cleanup now exists at the trace-coverage layer via
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_target_removed_of_card_eq`
and
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_prefers_target_to_current_of_card_eq`.
The blocker side now also has the membership bridge
`im05_mem_stableHusbands_iff_exists_stable_exception_match` and
`im05_not_mem_stableHusbands_iff_forall_stable_not_exception_match`,
converting between stable-husband membership/non-membership and direct
`m_match _ = some g` witness/exclusion forms.
The current one-stop remaining-obligation target is
`im05_Algorithm41SourceCompletionCertificate`; proving it discharges the
paper-facing output contract through
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate`.
The matched-final-preference premise now also has the one-stop paper-facing
wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalPref_of_card_eq`.
The paper-facing equal-size wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate_of_card_eq`
derives the initial-husband witness internally from equal cardinality and
all-acceptable preferences.
The second field now also has a paper-natural final target-blocking form:
`im05_SourceFinalNoninitialStableHusbandTargetBlocks`,
`im05_SourceFinalNoninitialStableHusbandTargetBlocks.finalPref`,
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_finalPref`,
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_finalPref`,
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_finalTargetBlocks_of_card_eq`,
`im05_Algorithm41SourceCompletionCertificate_of_finalTargetBlocks`, and
`im05_Algorithm41SourceCompletionCertificate_of_finalPref`, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks`.
There is also a direct backward-inclusion corollary,
`im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`,
for citing the stable-husbands-subset-output part alone, plus direct set
equality
`im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_finalTargetBlocks_of_card_eq`
and length equality
`im05_algorithm41SourceDivorceTargetAcceptedMen_length_eq_stableHusbands_card_of_finalTargetBlocks_of_card_eq`,
with order projection
`im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest_of_finalTargetBlocks_of_card_eq`.
Under all-acceptable preferences, the `valM` unmatched case in the
target-blocking predicate is now automatic, so the final-field proof can be
written as the matched-assignment preference obligation only.
The preferred paper endpoint is now the corresponding equal-size wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`.
This leaves the current Algorithm 4.1 endpoint as the one-step non-target
blocker exclusion plus proving that every non-initial stable husband would
strictly prefer `g` to his final target-divorced assignment.
The local and trace forms of the non-target blocker predicate are now connected
both ways by `im05_SourceTraceNonTargetBlockersNotStableHusbands_iff_stepBlockers`.
The local blocker predicate can also be discharged from the stronger
stable-matching exclusion interface
`im05_SourceStepNonTargetStableMatchExclusions` via
`im05_SourceStepNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`.
The trace-level version is packaged as
`im05_SourceTraceNonTargetStableMatchExclusions` and
`im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`.
At the invariant-preservation layer, the same condition now gives
`im05_SourceStepNonTargetRejectedPairExclusions_of_stableMatchExclusions` and
the prefix rejected-pair-impossibility wrappers ending in
`_of_traceStableMatchExclusions` and `_of_stepStableMatchExclusions_prefix`.
For a less over-strong non-target proof route, use
`im05_SourceStepNonTargetBlockingPreferences` and
`im05_SourceStepNonTargetRejectedPairExclusions_of_blockingPreferences`: these
ask directly for the blocking inequalities needed in the rejected/displaced
pair arguments. The corresponding trace and paper wrappers are
`im05_SourceTraceNonTargetBlockingPreferences`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceBlockingPreferences`, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceBlockingPreferences`.
The sharper local accepted-step variant is
`im05_SourceStepNonTargetBlockingPairPreferences`, which only asks for the
proposer-side inequality in candidate stable matchings that keep the displaced
current holder at the chosen non-target woman. It now also has trace,
full target-proposal, except-initial, and final-removal wrappers ending in
`BlockingPairPreferences`. The older stable-match-exclusion route now feeds
this sharper route through
`im05_active_proposer_prefers_chosen_in_stable_match_except_exception`,
`im05_SourceStepNonTargetBlockingPairPreferences_of_stableMatchExclusions`,
and
`im05_SourceTraceNonTargetBlockingPairPreferences_of_stableMatchExclusions`.
The broader direct blocking-preference route also coerces to the sharper route
via
`im05_SourceStepNonTargetBlockingPairPreferences_of_blockingPreferences` and
`im05_SourceTraceNonTargetBlockingPairPreferences_of_blockingPreferences`.
The source-faithful except-initial and final-removal endpoints are also
available through theorem names ending in
`_except_initial_of_traceBlockingPreferences` and
`_final_target_removed_of_stepBlockingPreferences_of_card_eq`.
For full target-proposal coverage with pair-level hypotheses, use
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceBlockingPairPreferences`
or the corresponding `_of_stepBlockingPairPreferences` wrapper.
The pair-level final-removal endpoint also has direct projections for backward
inclusion, output finset equality, output length, and worst-to-best order, with
names ending in
`_of_stepBlockingPairPreferences_finalTargetRemoved_of_card_eq`.
The broader blocking-preference final-removal endpoint has the analogous
projection family with names ending in
`_of_stepBlockingPreferences_finalTargetRemoved_of_card_eq`.
The preferred reduced contract is also bundled as
`im05_Algorithm41SourcePairCompletionCertificate`; the one-stop paper-facing
wrapper is
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairCompletionCertificate_of_card_eq`.
An even weaker rejection-side seam is now available:
`im05_SourceStepNonTargetBlockingPairWitnessPreferences` only asks, on rejected
non-target steps, for one prior proposer that forms the blocking pair in the
candidate stable matching. It has trace, full target-proposal, except-initial,
and final-removal wrappers ending in `BlockingPairWitnessPreferences`.
The compact witness-form remaining-obligation target is
`im05_Algorithm41SourcePairWitnessCompletionCertificate`, with one-stop wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`.
The target-only-prefix special case is closed by
`im05_SourceStepNonTargetStableMatchExclusions_of_target_chosen`,
`im05_SourceTraceNonTargetStableMatchExclusions_of_target_chosen_prefix`, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_target_chosen_prefix`.
The trace-coverage theorem also has direct stable-match-exclusion entry
points:
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceStableMatchExclusions`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepStableMatchExclusions`.
The current reduced endpoint can now use
`im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalPref`
or the paper-facing wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalPref_of_card_eq`.
The compact final-target-blocking route has the parallel constructor
`im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetBlocks`
and paper-facing endpoint
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`.
Final target-proposal removal now implies the compact final-target-blocking
field via
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_final_target_removed`,
with certificate and paper endpoints ending in
`_of_stableMatchExclusions_finalTargetRemoved`.
Conversely,
`im05_final_target_removed_of_SourceFinalNoninitialStableHusbandTargetBlocks`
and
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_final_target_removed`
show these final-field formulations are equivalent under the strict
all-acceptable assumptions.
It also exposes direct stable-match-exclusion projection corollaries for the
backward inclusion, finset equality, length equality, and worst-to-best order.

| Algorithm 4.2 | `im05_algorithm42FreshListSample`, `im05_algorithm42FreshListPMF`, `im05_algorithm42FreshListDraw`, `im05_listPrefixOmits`, `im05_listPrefixSet`, `im05_listPrefixOmits_zero`, `im05_listPrefixOmits_nested`, `im05_listPrefixOmits_succ_iff`, `im05_listPrefixOmits_iff_not_mem_prefixSet`, `im05_listPrefixSet_card_of_injective`, `im05_next_slot_not_mem_prefixSet_of_injective`, `paper_im05_algorithm4_2_filtered_draw_atom_formula`, `paper_im05_algorithm4_2_freshList_first_draw_atom_formula`, `paper_im05_algorithm4_2_freshList_zero_prefix_conditional_atom_formula`, `paper_im05_algorithm4_2_freshList_prefixSet_conditional_atom_formula`, `paper_im05_algorithm4_2_freshList_prefixSet_omit_conditional_atom_formula`, `paper_im05_algorithm4_2_freshList_omit_pos_of_full_support`, `paper_im05_algorithm4_2_freshList_prefix_omit_pos_of_full_support`, `paper_im05_algorithm4_2_freshList_event_prob_tendsto`, `paper_im05_algorithm4_2_freshList_omit_prob_tendsto`, `paper_im05_algorithm4_2_freshList_conditional_omit_tendsto`, `paper_im05_lemma4_3_next_hit_le_from_algorithm4_2_filtered_draw`, `paper_im05_lemma4_3_next_hit_le_from_prefix_state_bounds`, `paper_im05_lemma4_3_next_hit_le_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_conditional_prefix_omit_ge_of_next_hit_le`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_next_hit_bounds`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_algorithm4_2_prefix_sets`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_next_hit_bounds`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_product_absence_probability`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_states_product`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_sets_product`, `paper_im05_lemma4_3_absence_probability_ge_exp_rank_from_next_hit_bounds`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_next_hit_bounds`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_prefix_states_product`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_product`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_prefix_sets_product`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_prefix_sets_product_of_top_prefix_mass`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_freshList_ranked_tails_prefix_sets_product_of_top_prefix_mass`, `finiteWithoutReplacementPMF`, `finiteWithoutReplacementPMF_head_prob`, `finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`, `finiteWithoutReplacementPMF_omit_atom_pos`, `finiteWithoutReplacementPMF_event_prob_tendsto`, `finiteWeightedPMFExcluding_apply_toReal_eq_div_one_sub`, `pmfConditionalProb_le_of_state_refinement`, `pmfConditionalProb_tendsto_of_inter_tendsto_of_condition_tendsto`, `pmfProduct_prob_forall`, `im05_popularityRankTail_card`, `im05_popularityRankTail_popular` | partially formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Math/FiniteRanking.lean`; `EconCSLib/Foundations/Probability/Conditional.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Probability/Weighted.lean`; `EconCSLib/Foundations/Probability/WithoutReplacement.lean` | The concrete list-prefix event and prefix-set layers for a length-`k` one-man list are formalized. Per-prefix positive probability plus next-slot conditional hit bounds imply the one-man omission product, the all-men rank-power/exponential absence bounds, and the Lemma 4.3 expected-count lower bound. The Algorithm 4.2 filtered-draw atom formula is reusable as a finite weighted PMF law, and the concrete recursive fresh-list PMF now exists over structurally distinct lists with proved first-draw, zero-prefix, arbitrary positive prefix-set conditional atom formulas, atom-sum event probabilities, fixed-event convergence, and conditional omission convergence. Under full support and `k < #W`, full-list omission and every prefix-omission event have positive probability. Finite-state refinement lifts statewise prefix laws to the coarser prefix event, prefix-set wrappers derive `w ∉ previous` and available-mass positivity from realized prefix assumptions, independent identical one-man draws have finite-product wrappers, and ranked popularity tails supply the `rank-k` cardinality and pointwise popularity comparison. The top-`k` prefix mass comparison discharges the realized prefix-mass bound under distinct positive-support samples, and the concrete fresh-list ranked-tail wrapper now discharges the former `hcond_eq` stochastic obligation for Algorithm 4.2. |
| Equations (4.1)-(4.2) first-hit and expectation bounds | `paper_im05_equation4_1_weighted_first_hit_bound`, `paper_im05_equation4_1_conditional_probability_le_reciprocal`, `paper_im05_equation4_2_expectation_le_reciprocal`, `weight_share_le_inv_card_add_one_of_forall_le` | partially formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Math/FiniteSum.lean` | Formalizes the weighted finite race inequality behind the displayed conditional probability bound and the expectation lift: if every woman in `S_mu(g)` has probability at least `p_g`, then `g`'s weight share in `{g} ∪ S_mu(g)` is at most `1/(|S_mu(g)|+1)`; if the conditional event is bounded by that first-hit share, the exact reciprocal bound follows; and any pointwise conditional-probability bound by `1/(X_mu(g)+1)` integrates to `E[1/(X_mu(g)+1)]`. The remaining work is the Algorithm 4.2 stochastic first-hit construction connecting the weight share to `Pr[x_g > 1 | mu]`. |
| Lemma 4.1 | `paper_im05_lemma4_1_reciprocal_bound_from_variance`, `paper_im05_lemma4_1_algebra_from_lemma4_3`, `paper_im05_lemma4_1_from_variance_and_lemma4_3`, `paper_im05_lemma4_1_from_stable_sample_variance_and_lemma4_3`, `paper_im05_lemma4_1_from_negative_correlation_and_lemma4_3`, `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`, `paper_im05_lemma4_1_from_negative_correlation_and_algorithm4_2_freshList_lemma4_3`, `paper_im05_lemma4_1_from_algorithm4_2_freshList_conditional_and_lemma4_4`, `paper_im05_lemma4_1_from_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`, `paper_im05_lemma4_1_from_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`, `paper_im05_lemma4_1_from_algorithm4_2_freshList_full_support_permutation_limits_and_lemma4_4`, `paper_im05_lemma4_1_from_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`, `pmfVariance`, `pmfProb_abs_sub_mean_gt_le_variance_div_sq`, `pmfProb_lt_half_expectation_le_four_div_expectation_of_variance_le_expectation` | partially formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Probability/WithoutReplacement.lean` | Formalizes the source's Chebyshev/variance-to-reciprocal bridge: if `Var(Y_g) <= E[Y_g]`, `X_mu(g) >= Y_g`, and `E[Y_g] > 0`, then `E[1/(X_mu(g)+1)] <= 6/E[Y_g]`; composing with the Lemma 4.3 lower bound gives the displayed `12 exp(8nk/g)/g` reciprocal bound. A sampled-stable-matching wrapper now supplies `X_mu(g) >= Y_g` directly from Lemma 4.2. There is also a source-route wrapper that derives this bound from Lemma 4.3 plus pairwise negative correlation of the `Y_g` indicator events, a corrected tail-count wrapper that uses pairwise negative correlation only on the Lemma 4.3 rank-tail block, a concrete Algorithm 4.2 fresh-list wrapper that supplies the Lemma 4.3 lower bound directly, and a sharper full-support concrete wrapper that discharges positivity and reduces the remaining variance input to the paper's one-man Lemma 4.4 conditional comparison. The newest wrappers supply that comparison from explicit multiset approximation limits, concrete integer-multiset permutation event limits, finite permutation event limits, or finite-scale inequalities for approximating weight vectors plus pointwise weight convergence. The full lemma still needs Algorithm 4.2's concrete stable-matching random-variable construction; its published Lemma 4.4 variance input now has a validation issue because the arbitrary-`k` one-man negative-correlation claim is false at `k = 3`. |
| Lemma 4.2 | `paper_im05_lemma4_2_absent_popular_card_le_single_popular`, `paper_im05_lemma4_2_expected_absent_popular_le_expected_single_popular`, `paper_im05_lemma4_2_reciprocal_single_popular_le_absent_popular` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean` | Deterministic cardinality form under Lean's encoding of "not on any man's list" as strictly unacceptable to every man, plus finite sampled-market expectation and reciprocal wrappers: if every sample is paired with a stable matching, then expected `Y_g` is at most expected `X_mu(g)`, and the reciprocal expectation inequality used in Lemma 4.1 follows. The remaining caveat is wiring the paper's concrete Algorithm 4.2 market sample and matching choice into this generic wrapper. |
| Lemma 4.3 | `paper_im05_lemma4_3_previous_mass_le_top_mass_of_injection`, `paper_im05_lemma4_3_previous_mass_le_Q_of_top_injection`, `paper_im05_lemma4_3_previous_mass_le_top_mass_of_card_le_top_prefix`, `paper_im05_lemma4_3_previous_mass_le_Q_of_card_le_top_prefix`, `paper_im05_lemma4_3_realized_prefixSet_mass_le_Q_of_top_prefix_of_pos_support`, `paper_im05_lemma4_3_popularity_mass_bound_from_tail_set`, `paper_im05_lemma4_3_popularity_rank_bound`, `im05_popularityTopPrefix`, `im05_popularityRankTail`, `im05_popularityRankTail_card`, `im05_popularityRankTail_popular`, `im05_listPrefixSet`, `im05_listPrefixOmits_iff_not_mem_prefixSet`, `paper_im05_lemma4_3_conditional_omit_ge_top_mass_bound`, `paper_im05_lemma4_3_single_draw_omit_lower_bound`, `paper_im05_lemma4_3_conditional_single_draw_omit_lower_bound_from_rank_tail`, `paper_im05_lemma4_3_next_hit_upper_bound_from_rank_tail`, `paper_im05_lemma4_3_conditional_next_hit_le_from_rank_tail_formula`, `paper_im05_algorithm4_2_filtered_draw_atom_formula`, `paper_im05_algorithm4_2_freshList_zero_prefix_conditional_atom_formula`, `paper_im05_algorithm4_2_freshList_prefixSet_omit_conditional_atom_formula`, `paper_im05_lemma4_3_next_hit_le_from_algorithm4_2_filtered_draw`, `paper_im05_lemma4_3_next_hit_le_from_prefix_state_bounds`, `paper_im05_lemma4_3_next_hit_le_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_prefix_bounds`, `paper_im05_lemma4_3_conditional_prefix_omit_ge_of_next_hit_le`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_next_hit_bounds`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_algorithm4_2_prefix_sets`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_prefix_bounds`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_next_hit_bounds`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_sets_product`, `paper_im05_lemma4_3_product_absence_probability`, `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_states_product`, `paper_im05_lemma4_3_absence_probability_ge_exp_rank_from_rank_power`, `paper_im05_lemma4_3_absence_probability_ge_exp_rank_from_prefix_bounds`, `paper_im05_lemma4_3_absence_probability_ge_exp_rank_from_next_hit_bounds`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_prefix_bounds`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_next_hit_bounds`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_prefix_states`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_prefix_states_product`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_product`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_prefix_sets_product`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_prefix_sets_product_of_top_prefix_mass`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_freshList_ranked_tails_prefix_sets_product_of_top_prefix_mass`, `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_popularity_tails`, `finiteWeightedPMFExcluding_apply_toReal_eq_div_one_sub`, `finiteWithoutReplacementPMF_head_prob`, `finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`, `pmfConditionalProb_le_of_state_refinement`, `pmfProduct_prob_forall`, `pmfProb_ge_pow_of_nested_conditionalProb_ge`, `pmfConditionalProb_congr_of_condition`, `pmfConditionalProb_congr`, `pmfConditionalProb_compl_eq_one_sub_of_pos`, `one_sub_le_pmfConditionalProb_compl_of_conditionalProb_le`, `pmfExp_card_filter_ge_card_mul_of_forall_mem_prob_ge`, `finset_sum_le_sum_of_injOn_nonneg`, `finset_sum_le_sum_of_card_le_pairwise_sdiff`, `card_mul_le_sum_of_forall_le`, `le_div_card_of_sum_le_of_forall_le`, `exp_neg_two_div_le_one_sub_inv_of_two_le`, `exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le`, `lowerRankFinset_mono` | partially formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Math/FiniteRanking.lean`; `EconCSLib/Foundations/Probability/Conditional.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Probability/Weighted.lean`; `EconCSLib/Foundations/Probability/WithoutReplacement.lean`; `EconCSLib/Foundations/Math/FiniteSum.lean`; `EconCSLib/Foundations/Math/ExponentialBounds.lean` | Formalizes the summation core, deterministic popularity/rank algebra, and the deferred-decision product bridge. Top-block domination has explicit-injection and cardinal/ranked-top-prefix forms, and the realized prefix-mass bound is discharged for distinct positive-support samples from the top-`k` mass bound. Ranked popularity tails provide the `rank-k` witness cardinality and pointwise popularity comparison; the filtered one-step draw formula gives atom probability `p_w/(1-prevMass)`; finite-state refinement turns statewise prefix laws into the coarser next-hit bound; prefix-set wrappers derive `w ∉ previous` and available-mass positivity from realized prefix assumptions; the concrete recursive fresh-list sampler now proves the arbitrary positive prefix-set conditional atom law; nested prefix conditional lower bounds give the one-man product; finite product PMFs instantiate the all-men independence identity; and the exponential relaxation yields `exp(-4nk/w)` and the Lemma 4.3 expected-count endpoint. |
| Lemma 4.4 | `im05_namesBeforeFirst`, `im05_nameCountInWord`, `im05_nameCountInWord_eq_count_ofFn`, `im05_countVectorMultiset`, `im05_countVectorList`, `im05_countWeight`, `im05_countWeight_available_pos_of_count_pos`, `im05_count_pos_of_countWeight_available`, `im05_integerMultisetPermutationSample`, `im05_integerMultisetPermutationSample_nonempty`, `im05_integerMultisetPermutationList`, `im05_integerMultisetPermutationList_count`, `im05_kDistinctNamesBefore_excluding_imp`, `paper_im05_lemma4_4_multiset_event_inclusion_probability`, `paper_im05_lemma4_4_integerMultiset_event_inclusion_probability`, `paper_im05_lemma4_4_freshList_pairwise_negative_correlation_countWeight_two`, `paper_im05_lemma4_4_freshList_conditional_comparison_countWeight_two`, `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_scaled_count_negative_correlation_limits_two`, `paper_im05_lemma4_4_variance_le_expectation_from_freshList_scaled_count_negative_correlation_limits_two`, `im05_plackettLuce_k3_omission_negative_correlation_counterexample_scalar`, `im05_plackettLuce_k3_conditional_comparison_counterexample_scalar`, `im05_lemma4_4_variance_counterexample_scalar`, `paper_im05_lemma4_4_freshList_conditional_comparison_from_integerMultiset_erased_upper_bound`, `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_erased_upper_bounds_and_scaled_count_limits`, `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_erased_upper_bounds_and_scaled_count_limits_two`, `paper_im05_lemma4_4_variance_le_expectation_of_pairwise_negative_correlation`, `paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`, `paper_im05_lemma4_4_pairwise_negative_correlation_from_conditional`, `paper_im05_lemma4_4_variance_le_expectation_from_conditional`, `paper_im05_lemma4_4_all_men_probability_power_bound`, `paper_im05_lemma4_4_pairwise_negative_correlation_from_single_man`, `paper_im05_lemma4_4_pairwise_negative_correlation_from_single_man_conditional`, `paper_im05_lemma4_4_variance_le_expectation_from_single_man_conditional`, `paper_im05_lemma4_4_product_event_probability`, `paper_im05_lemma4_4_product_joint_event_probability`, `paper_im05_lemma4_4_pairwise_negative_correlation_from_single_man_conditional_product`, `paper_im05_lemma4_4_variance_le_expectation_from_single_man_conditional_product`, `paper_im05_lemma4_4_variance_le_expectation_from_freshList_multiset_limits`, `paper_im05_lemma4_4_variance_le_expectation_from_freshList_permutation_limits`, `paper_im05_lemma4_4_variance_le_expectation_from_freshList_integerMultiset_limits`, `paper_im05_lemma4_4_variance_le_expectation_from_freshList_weight_limits`, `finiteWithoutReplacementPMF_event_prob_succ_eq_sum_head`, `finiteWithoutReplacementPMF_omit_atom_succ_prob_eq_sum_head`, `finiteWithoutReplacementPMF_omit_pair_succ_prob_eq_sum_head`, `finiteWithoutReplacementPMF_event_prob_const_mul`, `finiteWithoutReplacementPMF_conditional_prob_const_mul`, `pmfConditionalProb`, `pmfConditionalProb_tendsto_of_inter_tendsto_of_condition_tendsto`, `pmfConditionalProb_le_of_inter_le_mul`, `pmfProb_not_and_not_le_mul_of_inter_le_mul`, `pmfProb_inter_le_mul_of_conditionalProb_le`, `pmfProduct_prob_forall`, `pmfProb_congr`, `pmfVariance_card_filter_le_pmfExp_card_filter_of_pairwise_inter_le_mul`, `pmfExp_card_filter_sq_eq_sum_pmfProb_inter`, `pmfVariance_eq_exp_sq_sub_sq_exp` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/Conditional.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Probability/Weighted.lean`; `EconCSLib/Foundations/Probability/WithoutReplacement.lean`; `EconCSLib/Foundations/Math/Asymptotics.lean` | The caveat is substantive: the printed unrestricted statement `Var(Y_g) <= E[Y_g]` is false for arbitrary nonuniform `D^k`, so this row does not claim the source statement as printed. Lean formalizes the variance conclusion from pairwise negative correlation, the corrected rank-tail replacement `paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`, source-route probability algebra, and scalar counterexamples including `im05_lemma4_4_variance_counterexample_scalar`. The finite multiset event inclusion is closed, limit-passing and product-PMF independence wrappers are closed, the `k = 0` and `k = 1` finite comparison cases are closed, the `k = 2` marginal finite law is closed, and support can now be derived from finite availability. The direct `k = 2` weighted-without-replacement negative-correlation route is also closed, including the raw-count conditional comparison, scaled-count limit wrapper, and independent-men variance endpoint. The source's conditioning-equals-deletion step is false for nonuniform weights, the erased-process upper bound is false, and the arbitrary-`k` one-man negative-correlation claim is false for the Plackett--Luce sampler at `k = 3`; `NegativeCorrelationCounterexample.md` records exact weights and probabilities. The downstream Theorem 3.1 repair still needs the stochastic tail negative-correlation or tail-variance input for the concrete fresh-list law. |
| Lemma 6.1 | `paper_im05_lemma6_1_from_lemma6_2` | conditional | `IM05MarriageHonestyStability/MainTheorems.lean` | Proves the paper's `E[1/(X+1)] <= (e^(k+1)+k^2)/n` conclusion from a Lemma 6.2 hypothesis and the closed Lemma 6.3 occupancy bound. The random-list proof of Lemma 6.2 is still open. |
| Lemma 6.2 | `paper_im05_lemma6_2_experiment_chain`, `paper_im05_lemma6_2_from_draw_redundant_pairs_experiments_of_four_le`, `paper_im05_lemma6_2_from_draw_usedBins_experiments_of_four_le` | conditional | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | Formalizes the expectation chain from the five experiments once the paper's monotonicity/equality/perturbation/occupancy-identification relations are supplied. The draw-prefix wrappers now combine the five-experiment chain with the validated `k >= 4` perturbation theorem, so the remaining obligations are exactly the concrete construction of Experiments 1-5 and the per-pair probability argument for Experiment 3. |
| Lemma 6.2, perturbation/union-bound route | `paper_im05_lemma6_2_perturbation_from_bad_event`, `paper_im05_lemma6_2_union_bound_pairs`, `im05_redundantProposalPair`, `im05_redundantPairIndex`, `im05_experiment3PrefixSample`, `im05_experiment3PrefixSampleRelabel`, `im05_experiment3_uniform_prefix_relabel_prob`, `im05_experiment3BadDrawEvent`, `im05_redundantSlot_relabel_iff`, `im05_redundantPairEvent_relabel_iff`, `im05_redundantPairBadEvent_relabel_iff`, `im05_experiment3BadDrawEvent_relabel_iff`, `occupancyFirstHitBalls_image_eq_usedBins`, `occupancyFirstHitBalls_card_eq_usedBins`, `im05_nonredundant_slots_eq_firstHitBalls`, `im05_nonredundant_slots_image_eq_usedBins`, `im05_nonredundant_slots_card_eq_usedBins`, `paper_im05_lemma6_2_usedBins_card_le_of_two_redundant_slots`, `paper_im05_lemma6_2_bad_draw_event_iff_exists_two_redundant_slots`, `paper_im05_lemma6_2_two_redundant_slots_of_redundant_pair_event`, `paper_im05_lemma6_2_usedBins_card_le_of_redundant_pair_event`, `paper_im05_lemma6_2_bad_draw_event_iff_exists_redundant_pair_event`, `paper_im05_lemma6_2_bad_draw_event_prob_eq_redundant_pair_exists`, `paper_im05_lemma6_2_bad_draw_event_prob_le_card_mul`, `paper_im05_lemma6_2_bad_draw_event_prob_le_k_sq_div`, `paper_im05_lemma6_2_redundantPairIndex_card`, `paper_im05_lemma6_2_redundant_pair_union_bound`, `paper_im05_lemma6_2_redundant_pair_count_bound`, `paper_im05_lemma6_2_choose_le_sq_of_four_le`, `paper_im05_lemma6_2_choose_le_sq_iff_four_le`, `paper_im05_lemma6_2_redundant_pair_count_bound_of_four_le`, `im05_earlierSlots_card`, `paper_im05_lemma6_2_prescribed_two_uniform_draws_prob`, `paper_im05_lemma6_2_prescribed_two_draw_slots_prob`, `paper_im05_lemma6_2_prescribed_two_man_draw_slots_prob`, `paper_im05_lemma6_2_two_draw_slots_collision_prob`, `paper_im05_lemma6_2_redundantSlot_prob_le_earlier_count_div`, `paper_im05_lemma6_2_redundantSlot_prob_le_slot_div`, `paper_im05_lemma6_2_two_uniform_draws_collision_prob`, `paper_im05_lemma6_2_two_uniform_draws_collision_prob_gt_inv_sq`, `paper_im05_lemma6_2_bad_draw_event_subset_redundant_pair_events`, `paper_im05_lemma6_2_perturbation_from_redundant_pairs`, `paper_im05_lemma6_2_perturbation_from_redundant_pairs_of_four_le`, `paper_im05_lemma6_2_perturbation_from_draw_redundant_pairs`, `paper_im05_lemma6_2_perturbation_from_draw_redundant_pairs_of_four_le`, `paper_im05_lemma6_2_perturbation_from_draw_usedBins`, `paper_im05_lemma6_2_perturbation_from_draw_usedBins_of_four_le` | conditional | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean`; `EconCSLib/Foundations/Probability/Occupancy.lean` | Formalizes the paper's negligible-perturbation structure: equality on good event `E`, finite union bound over men times unordered distinct pairs of first `k+2` proposal positions, and the algebraic route from per-pair `1/n^2` probabilities to `k^2/n`. The coarse `choose(k+2,2) <= k^2` side condition is explicit; Lean proves the exact threshold `choose(k+2,2) <= k^2 ↔ k >= 4`, plus paper-facing `k >= 4` wrappers for the redundant-pair and draw-prefix perturbation statements. The deterministic draw-prefix bridge is now exact and backed by reusable occupancy first-hit lemmas: non-redundant slots are precisely first appearances, the Experiment 3 bad-prefix event is equivalent both to existence of a man with two redundant slots and to existence of an indexed redundant-pair event, and this equivalence is lifted to a probability-level union-bound wrapper. The first-`k+2` draw-prefix sample space and uniform woman-relabeling probability wrapper are explicit. Redundant-slot, redundant-pair, indexed bad-pair, and used-bin bad-draw events are proved invariant under woman relabeling. The exact `1/n^2` probability is now proved for two prescribed independent uniform coordinates, two distinct slots in a first-`k+2` prefix, and two fixed man-slot coordinates in an uncurried all-men draw space. Lean also proves the honest one-slot redundancy bounds `Pr[slot redundant] <= #earlier/n = slot/n` and records that a plain two-slot/two-draw collision has probability `1/n`, strictly larger than `1/n^2` for `n > 1`; the remaining open step is a source-faithful reduction from the paper's redundant-pair event to a prescribed-coordinate event. |
| Lemma 6.2, Experiment 1-to-2 monotonicity | `im05_singleWomen`, `im05_absentWomen`, `paper_im05_experiment1_2_absent_card_le_single_count` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean` | Proves the deterministic count relation that women named by no man are single in any stable matching, under the Lean encoding of "not named" as unacceptable to all men. The finite random experiment tying this relation to `X1` and `X2` remains to be built. |
| Lemma 6.2, Experiment 2 identification | `im05_distinctWomanList`, `im05_experiment2Sample`, `im05_experiment2Names`, `im05_experiment2EmptyCountFromSample`, `im05_experiment2EmptyCountFromSample_relabel`, `im05_experiment2_uniform_sample_relabel_prob`, `im05_experiment2EmptyCount`, `paper_im05_experiment2_expectation_eq_occupancy`, `paper_im05_experiment2_expectation_eq_occupancy_of_card` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/Occupancy.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | Defines the paper's ordered without-replacement Experiment 2 sample space as one injective `Fin k -> W` list per man, uncurries it to the named man-slot assignment, and proves the empty-count statistic and uniform sample probabilities are invariant under woman relabeling. Also identifies a supplied `k`-slot-per-man assignment with the occupancy expectation `Y_{kn,n}` after relabeling. Remaining caveat: the without-replacement Experiment 2 law still must be coupled to the amnesiac Experiment 3 stopping process; the occupancy identification is for supplied assignments/with-replacement occupancy, not a replacement for that source coupling. |
| Lemma 6.2, Experiment 2-to-3 equality | `paper_im05_experiment2_3_empty_count_eq_of_usedBins_eq`, `paper_im05_experiment2_3_reciprocal_expectation_eq_of_usedBins_eq`, `occupancyEmptyBins_card_eq_of_usedBins_eq` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/Occupancy.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | Proves the deterministic equality core and its reciprocal-expectation lift: coupled experiments with the same used-women set have the same unnamed-women count and hence the same `E[1/(X+1)]`. The remaining caveat is the probabilistic/deferred-decisions construction showing the paper's Experiment 2 and Experiment 3 are coupled with the same used-women set. |
| Lemma 6.2, Experiment 4-to-5 monotonicity | `paper_im05_experiment4_5_empty_count_mono`, `paper_im05_experiment4_5_empty_count_mono_of_slot_map`, `paper_im05_experiment4_5_reciprocal_expectation_mono`, `paper_im05_experiment4_5_reciprocal_expectation_mono_of_slot_map`, `occupancyUsedBins_comp_subset` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/Occupancy.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | Proves the deterministic `X4 >= X5` empty-count comparison from the source's used-bin subset relation, closes the common coupling case where Experiment 4's slots are read from Experiment 5's `k+1` slots by a slot map, and lifts both forms to reciprocal expectations. Still needs the concrete stopping-time construction of Experiment 4's slot type/map. |
| Lemma 6.2, Experiment 5 identification | `im05_experiment5Sample`, `im05_experiment5Names`, `im05_experiment5EmptyCountFromSample`, `im05_experiment5EmptyCountFromSample_relabel`, `im05_experiment5_uniform_sample_relabel_prob`, `im05_experiment5EmptyCount`, `paper_im05_experiment5_expectation_eq_occupancy`, `paper_im05_experiment5_expectation_eq_occupancy_of_card` | formalized with caveat | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/Occupancy.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | Proves the source claim `X5 = Y_{(k+1)n,n}` at the expectation level and now defines the explicit with-replacement Experiment 5 sample space, its uncurried names, empty-count statistic, and uniform woman-relabeling probability wrapper. The paper-facing cardinality wrapper needs only `#men = n` and `#women = n`; the remaining caveat is that the concrete Experiment 5 random variables still need to be wired into the full Lemma 6.2 construction. |
| Lemma 6.3 | `paper_im05_lemma6_3_occupancy_reciprocal_bound`, `paper_im05_lemma6_3_k_plus_one_n_bound` | formalized | `IM05MarriageHonestyStability/MainTheorems.lean`; `EconCSLib/Foundations/Probability/Occupancy.lean`; `EconCSLib/Foundations/Probability/FiniteExpectation.lean` | None; proves the paper's `E[1/(Y_{m,n}+1)] <= exp(m/n)/n` bound for the uniform occupancy model. The reusable proof uses a one-ball recurrence and geometric-to-exponential bound rather than the source's inclusion-exclusion derivation. |
| Appendix Lemmas A.1-A.2 | none yet | not started | none | Likely separate finite random matching/monotonicity layer after the main theorem path. |

## Current Next Target

Algorithm 4.2's positive-prefix Markov law is now closed for the recursive
fresh-list PMF through
`finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding` and the
paper-facing
`paper_im05_algorithm4_2_freshList_prefixSet_omit_conditional_atom_formula`.
The Lemma 4.3 ranked-tail product route now has a concrete fresh-list wrapper
for the explicit tail count, not only the unrestricted absent count. Lemma 4.1
has corrected tail-count concrete wrappers through pairwise negative
correlation, one-man conditional comparison, full support, multiset limits, and
pointwise weight limits. Fixed fresh-list event convergence and conditional
omission convergence are closed for pointwise-convergent approximating weight
vectors, and the tail-only wrappers avoid requiring the false all-pairs
conditional comparison.

The immediate next target is now the stochastic input to the corrected Lemma
4.1 variance route. The `k = 2` direct route is closed, including raw-count,
scaled-count, and independent-men variance endpoints, but the arbitrary-`k`
one-man negative-correlation claim is false for the recursive fresh-list law at
`k = 3`, and `LEMMA4_4_COUNTEREXAMPLE_REPORT.md` gives a standalone finite
counterexample to Lemma 4.4 as printed. The paper's Theorem 3.1 branch
therefore cannot be completed faithfully from the published Lemma 4.4 proof.
The patched replacement is an explicit tail-count variance bridge:
`paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`
and
`paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`.
These count only the rank-tail block used by Lemma 4.3's lower-bound range and
are documented as a proof-strategy deviation in `FINAL_VALIDATION_REPORT.md`
and `NEXT_AGENT_HANDOFF.md`. The concrete repaired route now also includes
`paper_im05_lemma4_3_tail_expected_absent_count_lower_bound_from_algorithm4_2_freshList_rank_indices_prefix_sets_product_of_top_prefix_mass`,
the `im05_rankIndexBlock` helpers for contiguous `Fin N` rank tails and their
Lemma 4.3 side conditions, including the count bridge
`im05_rankIndexBlock_filter_card_le_lowerRankFinset_filter_card`,
the source-range shortcut `im05_sourceRankTailBlock` with
`im05_sourceRankTailBlock_tail_conditions`,
`paper_im05_lemma4_1_from_tail_negative_correlation_and_algorithm4_2_freshList_rank_indices_lemma4_3`,
`paper_im05_lemma4_1_from_tail_variance_factor_and_algorithm4_2_freshList_rank_indices_lemma4_3`,
`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_conditional_and_lemma4_4`,
`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_multiset_limits_and_lemma4_4`,
`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_weight_limits_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_pairwise_negative_correlation_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`,
`paper_im05_sourceRankTailBlock_freshList_conditional_from_pairwise_negative_correlation`,
`paper_im05_lemma4_1_from_tail_negative_correlation_and_algorithm4_2_freshList_lemma4_3`,
`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`,
`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`,
and
`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`.
There is also a constant-factor fallback,
`paper_im05_lemma4_1_from_tail_variance_factor_and_lemma4_3`, for a direct
bound `Var(Y_tail) <= C * E[Y_tail]`. The remaining proof obligation is to
establish either tail negative correlation or a direct constant-factor
tail-variance bound for the concrete fresh-list law.
`TailVarianceExploration.md` records non-proof brute-force searches that found
no tail positive covariance once both targets are past rank `2k`; it should be
treated only as guidance for the next formal target. The current finite
induction scaffolding is compiled in
`im05_listPrefixOmits_finCons_succ_iff`,
`im05_finiteWithoutReplacementPMF_listPrefixOmits_succ_prob_eq_sum_head`,
`im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_prob_eq_sum_head`,
`im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_negative_correlation_from_first_step`,
`im05_firstStepOmitMarginalSum`, `im05_firstStepOmitPairProductSum`,
`im05_firstStepOmitMarginalSum_eq_prob`,
`im05_firstStepHeadWeight`,
`im05_firstStepResidualOmitProb`,
`im05_firstStepResidualSpreadSum`,
`im05_firstStepResidualSpreadSum_comm`,
`im05_firstStepResidualSpreadSum_nonneg_of_pairwise_opposite`,
`im05_firstStepResidualSpreadSum_eq_two_mul_gap`,
`im05_firstStepResidualSpreadSum_nonneg_iff`,
`im05_firstStepResidualSpreadSum_nonneg_zero_of_ne`,
`im05_firstStepHeadWeight_sum_eq_one`,
`im05_firstStepHeadWeight_nonneg`,
`im05_firstStepHeadWeight_le_one`,
`im05_firstStepResidualOmitProb_eq_zero_of_head_eq`,
`im05_firstStepResidualOmitProb_eq_prob_of_head_ne`,
`im05_firstStepResidualOmitProb_nonneg`,
`im05_firstStepResidualOmitProb_le_one`,
`im05_firstStepOmitMarginalSum_eq_headWeight_residual`,
`im05_firstStepOmitPairProductSum_eq_headWeight_residual_product`,
`im05_firstStepOmitMarginalSum_nonneg`,
`im05_firstStepOmitPairProductSum_nonneg`,
`im05_firstStepOmitPairProductSum_comm`,
`im05_firstStepOmitMarginalSum_eq_one_of_mem_forbidden`,
`im05_firstStepOmitPairProductSum_eq_marginal_of_left_mem_forbidden`,
`im05_firstStepOmitPairProductSum_eq_marginal_of_right_mem_forbidden`,
`im05_firstStepOmitPairProductSum_le_mul_of_available_firstStep`,
`im05_firstStepOmitMarginalSum_le_one`,
`im05_firstStepOmitPairProductSum_le_marginal_left`,
`im05_firstStepOmitPairProductSum_le_marginal_right`,
`im05_weighted_opposite_spread_identity`,
`im05_weighted_product_sum_le_product_sums_of_opposite_spread_nonneg`,
`im05_weighted_product_sum_le_product_sums_of_pairwise_opposite`,
`im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread_sum_nonneg`,
`im05_firstStepOmitPairProductSum_le_mul_of_residual_spread_sum_nonneg`,
`im05_firstStepOmitPairProductSum_le_mul_of_residualSpreadSum_nonneg`,
`im05_firstStepOmitPairProductSum_le_mul_of_residual_pairwise_opposite`,
`im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread`,
`im05_omissionPairNegativeCorrelation`, `im05_tailDepth`,
`im05_omissionPairNegativeCorrelation_of_tailDepth_firstStep_family`,
`im05_omissionPairNegativeCorrelation_of_tailDepth_positive_firstStep_family`,
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStep_firstStep_family`,
`im05_omissionPairNegativeCorrelation_two_of_ne`,
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_firstStep_family`,
`im05_omissionPairNegativeCorrelation_of_left_mem_forbidden`,
`im05_omissionPairNegativeCorrelation_of_right_mem_forbidden`,
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_firstStep_family`,
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_residual_spread_family`,
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_firstStep_averaging`,
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_available_firstStep_averaging`,
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_firstStep_averaging`,
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_available_firstStep_averaging`,
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_residual_spread_averaging`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_firstStep_averaging_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_available_firstStep_averaging_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residual_spread_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residualSpreadSum_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_firstStep_averaging_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_available_firstStep_averaging_and_lemma4_4`,
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_residualSpreadSum_and_lemma4_4`,
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_firstStep_family`,
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_positive_firstStep_family`,
and
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_firstStep_family`.
The corresponding available-target source wrapper is
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_firstStep_family`.
The exact residual-spread source wrapper is
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_residual_spread_family`.
The generic two-draw weighted-without-replacement omission NC base is now
closed.  The strongest compiled reduction now requires only the compact
first-step averaging inequality for residual lengths at least two and only in
states where both targets are still available.  Already-forbidden boundary
states are now closed internally because the relevant omission event is
certain, and the compact first-step sums have matching boundary equalities.
The new Lemma 4.1 wrapper composes that available-target input
directly to the corrected source-range reciprocal bound for the full-support
fresh-list law.  The generic Algorithm 4.2 wrappers are the right entrypoints
when finite approximation targets are known to satisfy `im05_tailDepth` but
are not definitionally the source rank block; the weight-limit wrapper composes
such finite-scale tail-depth facts and first-step averaging, including the
available-target variant, all the way to the corrected Lemma 4.1 endpoint.

The next independent main branch is Algorithm 4.1/Theorem 4.1.  The corrected
target-divorcing accepted-men trace is now the active source-facing endpoint;
the older non-divorcing source-held-men trace should be treated only as
scaffold and blocking-pair proof infrastructure.  The strongest current
one-stop paper wrapper is
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`,
so a future proof should target
`im05_Algorithm41SourcePairWitnessCompletionCertificate` rather than rebuild
the trace.  For the uniform Theorem 3.2 branch, the concrete Experiment 3
process and source-faithful per-index redundant-pair probability reduction
remain open.
