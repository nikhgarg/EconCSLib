# IM05 Proof Strategy

This is a live scratch plan for finishing the Immorlica--Mahdian paper. It is
not a replacement for the README theorem ledger; it records the mathematical
route and the current strategic priority when Lean needs a proof plan outside
the elaborator.

## Current State

The Algorithm 4.2 list sampler is now concrete: the recursive fresh-list PMF
has first-draw, zero-prefix, and arbitrary positive-prefix conditional atom
laws. Under full support and `k < #W`, every full-list omission and prefix
omission event has positive probability. Its atom formula, event-probability
atom sum, fixed-event convergence theorem, and conditional-omission convergence
wrappers are also formalized. The Lemma 4.3 ranked-tail/product route uses the
concrete prefix law, so the former statewise filtered-draw stochastic assumption
is closed.

The Lemma 4.1 Chebyshev/variance algebra is also closed. The remaining
Theorem 3.1 branch is therefore concentrated in three named source seams, with
Lemma 4.4 now routed through a corrected tail-count deviation rather than the
printed unrestricted variance lemma:

1. Algorithm 4.1 / Theorem 4.1: the output-contract wrapper, abstract
   strict-preference list existence theorem, arbitrary-start DA run, divorce
   state, target-exception rejection invariant, and IM05 resumed-run/held-men
   prefix wrappers are formalized; the resumed run has an explicit finite
   termination horizon and closed target-exception invariant preservation.
   The concrete held-men list is nodup and ordered worst-to-best for `g`.
   Source audit caveat: the current resumed `DAState` trace is only a scaffold,
   because the paper has `g` remember the best proposer so far after each
   divorce and reject future suitors below that standard.  The current state
   only stores the current match, so a faithful trace needs an explicit
   target-threshold field before proving the membership equality with the
   stable-husband set.  The first minimal threshold primitives are now
   `im05_algorithm41TargetAccepts`,
   `im05_algorithm41TargetStandardAfterAccept`, and
   `im05_algorithm41TargetStandard_value_mono_of_accepts`.  The proposal-history
   side of the source rule is now also explicit:
   `im05_algorithm41HasProposedTo`, `im05_algorithm41HistoryAccepts`,
   `im05_algorithm41BestProposedSoFar`,
   `im05_algorithm41BestProposedSoFar_after_history_accept`, and
   `im05_algorithm41HistoryAccepts_of_bestProposedSoFar_of_targetAccepts`.
   The compatibility bridge for non-target women is
   `im05_algorithm41HistoryAccepts_of_womanRejectionInvariantExcept_current_lt`:
   under the target-exception rejection invariant, current-match acceptance
   implies the source history acceptance test for every woman other than the
   exceptional target.  The chosen-proposal source seam is packaged as
   `im05_algorithm41SourceStepAccepts`, with wrappers for target-standard
   acceptance and non-target current-match acceptance.  The one-step transition
   `im05_algorithm41SourceStep` now uses this source accept predicate and has
   the basic proposal-history progress lemmas
   `im05_algorithm41SourceStep_m_proposals_chosen` and
   `im05_algorithm41SourceStep_records_chosen_proposal`.  The source run now
   has named finite-run/final-state/held-men wrappers, source-step preservation
   of the full target-exception invariant package on all-acceptable domains,
   source-final stable-except-target semantics, preservation of a target
   best-so-far proposer, preservation that any current target holder is
   best-so-far, preservation of a nonnegative target best-so-far proposer from
   the initial DA match, target held-value monotonicity along the source run,
   a proof that any source final target holder is a stable husband, and a
   source-held-men worst-to-best output certificate conditional only on the
   remaining source-held-men/stable-husbands membership equality.
   Important correction after rechecking the paper: Step 4(b) immediately sends
   `w = g` acceptances back to Step 2, where the accepted man is output and
   divorced. The non-divorcing source held-men trace above is therefore still a
   scaffold. The corrected surface is now
   `im05_algorithm41SourceStepTargetAccepted`,
   `im05_algorithm41SourceStepDivorceTarget`,
   `im05_algorithm41SourceDivorceTargetStateAfterSteps`, and
   `im05_algorithm41SourceDivorceTargetAcceptedMen`; it records target
   acceptance events and immediately divorces the target while preserving the
   finite proposal-count termination bound.  The source accept test is now
   proved equivalent to ordinary DA under full invariants
   (`im05_algorithm41SourceStepAccepts_iff_daStepChosenAccepts_of_invariants`,
   `im05_algorithm41SourceStep_eq_daStep_of_invariants`) and under
   target-exception invariants for non-target chosen women
   (`im05_algorithm41SourceStepAccepts_iff_daStepChosenAccepts_of_invariantsExceptWoman_nonTarget`,
   `im05_algorithm41SourceStep_eq_daStep_of_invariantsExceptWoman_nonTarget`).
   This closes the ordinary-DA current-match-order bridge from the initial DA
   state through the target-divorced start:
   `im05_deferredAcceptanceState_currentMatchOrder_of_allPairsAcceptable`,
   `im05_algorithm41DivorcedState_currentMatchOrder_of_allPairsAcceptable`, and
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_currentMatchOrder_of_allPairsAcceptable`.
   The backward-inclusion surface is now packaged as
   `im05_stableHusband_target_proposal_mem_sourceDivorceTargetAcceptedMen_of_trace_rejected_package_of_allPairsAcceptable`,
   `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_trace_target_proposals`,
   and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals`.
   Target-exception rejected-pair preservation is automatic for target-only
   active prefixes via
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_target_chosen_prefix`;
   the general non-target-step preservation is isolated by
   `im05_SourceStepNonTargetRejectedPairExclusions`,
   `im05_SourceStepNonTargetRejectedPairExclusions_of_full_rejectedPairImpossible`,
   `im05_algorithm41SourceStepDivorceTarget_preserves_rejectedPairImpossibleExceptWoman_of_stepNonTargetExclusions`,
   and
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepNonTargetExclusions_prefix`.
   The strongest current paper-facing bridge is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`:
   prove per-step non-target exclusions plus stable-husband target-proposal
   coverage, and Theorem 4.1's corrected accepted-men output contract follows.
   The per-step exclusion predicate is further reduced to exception-partner
   side conditions by
   `im05_prior_proposer_prefers_woman_in_stable_match_except_exception`,
   `im05_accepted_proposer_blocks_displaced_match_except_exception`,
   `im05_algorithm41SourceStep_nonTarget_reject_exclusion_of_prior_not_exception`,
   `im05_algorithm41SourceStep_nonTarget_accept_displaced_exclusion_of_proposer_not_exception`,
   `im05_SourceStepNonTargetRejectedPairExclusions_of_exception_partner_exclusions`,
   and
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_exception_partner_exclusions_prefix`.
   The readable prefix predicate and final conditional endpoint are
   `im05_SourceTraceExceptionPartnerExclusions`,
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceExceptionPartnerExclusions`,
   and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceExceptionPartnerExclusions`.
   A still cleaner reduction is now compiled:
   `im05_SourceStepNonTargetBlockersNotStableHusbands` states the two
   non-target blocker obligations as one-step exclusions from `g`'s
   stable-husband set,
   `im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers` lifts
   these one-step obligations across the prefix, and
   `im05_SourceTraceNonTargetBlockersNotStableHusbands` records the resulting
   trace condition,
   `im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`
   converts them to exception-partner exclusions, and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_nonTargetBlockersNotStableHusbands`
   packages the full corrected output contract from that stable-husband-exclusion
   condition plus target-proposal coverage.  The wrapper
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`
   starts directly from the one-step predicate.
   The coverage side is now source-shaped too: the initial DA husband is already
   output before the corrected divorce/proposal loop, so the narrow coverage
   predicate is
   `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`.  The
   strongest current endpoint is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`:
   prove one-step blocker exclusions plus target-proposal coverage for every
   stable husband except the initial DA husband.
   That coverage can now be supplied by a final proposal-set condition:
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_removed_proposal_exists_chosen`
   extracts a chosen proposal from a removed proposal opportunity, and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`
   proves the output contract from one-step blocker exclusions plus the fact
   that each non-initial stable husband starts with `g` available and ends with
   `g` removed from his proposal set.
   The start-available half is now closed by
   `im05_noninitial_stableHusband_mem_divorced_proposals`; the strongest current
   endpoint is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands`,
   which leaves only one-step blocker exclusions and final removal of `g` from
   each non-initial stable husband's proposal set.
   Final removal can now be proved from a final-match preference condition:
   `im05_not_mem_proposals_of_terminated_prefers_target_to_current` is the
   generic terminal-state lemma, and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands`
   packages the current strongest final endpoint.
   The final-removal and final-preference endpoints also have equal-size
   wrappers ending in `_of_card_eq`, removing the explicit initial-husband
   witness at those intermediate paper-facing layers.
   The trace-coverage layer has matching equal-size wrappers:
   `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_target_removed_of_card_eq`
   and
   `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_prefers_target_to_current_of_card_eq`.
   For the blocker predicate, use
   `im05_mem_stableHusbands_iff_exists_stable_exception_match` and
   `im05_not_mem_stableHusbands_iff_forall_stable_not_exception_match` to move
   between membership/non-membership in `im05_stableHusbands` and direct
   matching witness/exclusion forms for `g`.
   The trace and per-step versions of the blocker predicate are equivalent via
   `im05_SourceTraceNonTargetBlockersNotStableHusbands_iff_stepBlockers`.
   To prove a local blocker package, it is enough to prove the stronger direct
   stable-matching exclusion predicate
   `im05_SourceStepNonTargetStableMatchExclusions` and apply
   `im05_SourceStepNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`.
   For a whole prefix, use `im05_SourceTraceNonTargetStableMatchExclusions` and
   `im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`.
   The same reduced condition now feeds the lower rejected-pair preservation
   layer through
   `im05_SourceStepNonTargetRejectedPairExclusions_of_stableMatchExclusions`
   and
   `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceStableMatchExclusions`.
   If the stable-match-exclusion route is too strong, use
   `im05_SourceStepNonTargetBlockingPreferences` instead; it asks directly for
   the man-side blocking inequalities and feeds
   `im05_SourceStepNonTargetRejectedPairExclusions_of_blockingPreferences`.
   The sharper local variant is
   `im05_SourceStepNonTargetBlockingPairPreferences`: on accepted non-target
   steps it only asks for the proposer-side inequality after assuming the
   displaced pair still appears in the candidate stable matching. Prefer the
   trace/final-removal wrappers ending in `BlockingPairPreferences` when using
   this sharper route. If you have the stronger stable-match-exclusion
   condition, convert it to the sharper route with
   `im05_SourceStepNonTargetBlockingPairPreferences_of_stableMatchExclusions`
   or the trace lift
   `im05_SourceTraceNonTargetBlockingPairPreferences_of_stableMatchExclusions`;
   the man-side active-proposer bridge is
   `im05_active_proposer_prefers_chosen_in_stable_match_except_exception`.
   If you have the broader direct blocking-preference predicate instead, use
   `im05_SourceTraceNonTargetBlockingPairPreferences_of_blockingPreferences`
   to enter the sharper pair-level route without reproving anything.
   The trace-level paper route is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceBlockingPreferences`.
   The pair-level analogue is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceBlockingPairPreferences`,
   with a step-hypothesis wrapper ending in `_of_stepBlockingPairPreferences`.
   When only a component of the output contract is needed, use the pair-level
   final-removal projection lemmas ending in
   `_of_stepBlockingPairPreferences_finalTargetRemoved_of_card_eq`, or the
   broader blocking-preference analogues ending in
   `_of_stepBlockingPreferences_finalTargetRemoved_of_card_eq`.
   For a compact remaining-obligation target, prove
   `im05_Algorithm41SourcePairCompletionCertificate` and then call
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairCompletionCertificate_of_card_eq`.
   If the rejection branch cannot prove every better prior proposer blocks,
   switch to the weaker witness route:
   `im05_SourceStepNonTargetBlockingPairWitnessPreferences`.  Its rejected
   branch only asks for one prior proposer that forms a blocking pair in the
   candidate stable matching, and it has final-removal and trace wrappers
   ending in `BlockingPairWitnessPreferences`.  The compact target for this
   route is `im05_Algorithm41SourcePairWitnessCompletionCertificate`, with
   one-stop wrapper ending in `_of_pairWitnessCompletionCertificate_of_card_eq`.
   For source-faithful use, prefer
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_traceBlockingPreferences`
   or the final-removal wrapper ending in
   `_final_target_removed_of_stepBlockingPreferences_of_card_eq`.
   If every active prefix step chooses `g`, use
   `im05_SourceTraceNonTargetStableMatchExclusions_of_target_chosen_prefix` or
   the paper-facing target-only-prefix wrapper; the non-target side is then
   vacuous.
   The trace-coverage route now has direct paper-facing wrappers from the
   same reduced condition:
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceStableMatchExclusions`
   and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepStableMatchExclusions`.
   The combined reduced endpoint is
   `im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalPref`,
   with paper-facing wrapper
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalPref_of_card_eq`.
   The compact final-target-blocking variant is also packaged by
   `im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetBlocks`
   and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`.
   Final target-proposal removal now gives that compact final field through
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_final_target_removed`,
   and the combined endpoint is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetRemoved_of_card_eq`.
   The reverse direction is also closed:
   `im05_final_target_removed_of_SourceFinalNoninitialStableHusbandTargetBlocks`
   and
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_final_target_removed`.
   Use the `_of_stableMatchExclusions_finalTargetBlocks_of_card_eq` projection
   lemmas when only the backward inclusion, finset equality, length equality,
   or worst-to-best order is needed.
   For future work, target the bundled certificate
   `im05_Algorithm41SourceCompletionCertificate`; the wrapper
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate`
   turns that certificate into the paper-facing output contract.
   The matched-final-preference premise has a direct paper-facing wrapper:
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalPref_of_card_eq`.
   The equal-size wrapper
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate_of_card_eq`
   now supplies the initial-husband witness internally from equal cardinality
   and all-acceptable preferences.
   The final-match field of that certificate now has a compact target-blocking
   form:
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks`,
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks.finalPref`,
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_finalPref`,
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_finalPref`,
   `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_finalTargetBlocks_of_card_eq`,
   `im05_Algorithm41SourceCompletionCertificate_of_finalTargetBlocks`, and
   `im05_Algorithm41SourceCompletionCertificate_of_finalPref`, and
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks`.
   Use
   `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`
   when only the backward inclusion is needed, and
   `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_finalTargetBlocks_of_card_eq`
   or
   `im05_algorithm41SourceDivorceTargetAcceptedMen_length_eq_stableHusbands_card_of_finalTargetBlocks_of_card_eq`
   when direct set or length equality is needed, and
   `im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest_of_finalTargetBlocks_of_card_eq`
   when only the order proof is needed.
   Under all-acceptable preferences, the `valM` unmatched case in
   `im05_SourceFinalNoninitialStableHusbandTargetBlocks` is automatic, so it is
   enough to prove the matched-final-assignment preference statement.
   Prefer the equal-size final-block wrapper
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`
   for source-shaped paper use.
   This is the preferred Algorithm 4.1 endpoint: prove the one-step
   non-target blocker exclusions and prove that every non-initial stable
   husband would strictly prefer `g` to his final target-divorced assignment.
2. Lemma 4.2: connect the stable-matching random variable `X_mu(g)` to the
   absent-popular-women count `Y_g` in the concrete random market.
3. Lemma 4.4: prove a valid stochastic input for the tail-count bridge
   `paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`,
   then feed it through
   `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`, or prove
   a direct constant-factor tail variance bound and feed it through
   `paper_im05_lemma4_1_from_tail_variance_factor_and_lemma4_3`.

The uniform Theorem 3.2 branch is separate. Lemma 6.3 and most deterministic
Experiment 2--5 bridges are closed, but Experiment 3 still needs the
source-faithful reduction from its redundant-pair event to a prescribed-pair
probability.

## Fastest Route

The fastest Theorem 3.1 route is to keep following the named Lemma 4.1 chain,
with the corrected tail-count variance bridge replacing the printed Lemma 4.4:

Algorithm 4.2 prefix law -> Lemma 4.3 tail lower bound -> corrected tail
variance bound -> Lemma 4.1 reciprocal bound -> Theorem 4.1/Algorithm 4.1 ->
Theorem 3.1.

The active Lean composition target is now the stochastic input to the corrected
tail-count bridge.  The generic bridge is already formalized:

`paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`

and its Lemma 4.1 composition endpoint is:

`paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`.

Instantiate the explicit `tail : Finset I` with the rank block used in Lemma
4.3's lower-bound sum, then prove either pairwise negative correlation inside
that tail or a direct variance bound for the concrete Algorithm 4.2 fresh-list
law.

The concrete Algorithm 4.2 tail route is also wired now.  Use these wrappers
instead of the older all-pairs source-route wrappers:

`paper_im05_lemma4_3_tail_expected_absent_count_lower_bound_from_algorithm4_2_freshList_ranked_tails_prefix_sets_product_of_top_prefix_mass`

`paper_im05_lemma4_3_tail_expected_absent_count_lower_bound_from_algorithm4_2_freshList_rank_indices_prefix_sets_product_of_top_prefix_mass`

`im05_rankIndexBlock` with its card/start/end lemmas, plus
`im05_rankIndexBlock_card_real`,
`im05_rankIndexBlock_card_ge_half`,
`im05_rankIndexBlock_half_le_rank`,
`im05_rankIndexBlock_two_mul_k_lt_rank`, and
`im05_rankIndexBlock_tail_conditions`, builds concrete contiguous `Fin N`
rank-index tails and discharges the repeated Lemma 4.3 side conditions.
`im05_rankIndexBlock_filter_card_le_lowerRankFinset_filter_card` connects
such a rank-index tail count to the lower-rank woman count used by
Lemma 4.2-style `X_mu(g) >= Y_g` domination.
For the exact final Lemma 4.3 summation range, use
`im05_sourceRankTailBlock`, `im05_sourceRankTailBlock_tail_conditions`, and
`im05_sourceRankTailBlock_filter_card_le_lowerRankFinset_filter_card`; this
packages the zero-based rank block `g / 2, ..., g - 1` and the arithmetic from
`g > 4k`.

`TailVarianceExploration.md` records small brute-force Plackett--Luce searches.
It is not a proof, but it found no positive covariance inside tails with
one-indexed rank greater than `2k`, so the exact tail negative-correlation
target remains plausible.

The finite induction route now has compiled first-step scaffolding:
`im05_listPrefixOmits_finCons_succ_iff`,
`im05_finiteWithoutReplacementPMF_listPrefixOmits_succ_prob_eq_sum_head`,
`im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_prob_eq_sum_head`,
and
`im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_negative_correlation_from_first_step`.
The compact API is now `im05_firstStepOmitMarginalSum`,
`im05_firstStepOmitPairProductSum`,
`im05_firstStepOmitMarginalSum_eq_prob`,
`im05_firstStepOmitMarginalSum_nonneg`,
`im05_firstStepOmitPairProductSum_nonneg`, and
`im05_omissionPairNegativeCorrelation`.  The base cases
`im05_omissionPairNegativeCorrelation_zero` and
`im05_omissionPairNegativeCorrelation_one_of_ne` are closed.  The deterministic
tail-depth layer is `im05_highWeightAvailableSet`, `im05_tailDepth`,
`im05_tailDepth_after_insert_of_tailDepth_succ`,
`im05_sourceRankTailBlock_tailDepth`, and
`im05_sourceRankTailBlock_tailDepth_after_one_delete_name`.
The compact first-step boundary algebra is now also available:
`im05_firstStepHeadWeight`, `im05_firstStepResidualOmitProb`,
`im05_firstStepHeadWeight_sum_eq_one`,
`im05_firstStepHeadWeight_nonneg`, `im05_firstStepHeadWeight_le_one`,
`im05_firstStepResidualOmitProb_eq_zero_of_head_eq`,
`im05_firstStepResidualOmitProb_eq_prob_of_head_ne`,
`im05_firstStepResidualOmitProb_nonneg`,
`im05_firstStepResidualOmitProb_le_one`,
`im05_firstStepOmitMarginalSum_eq_headWeight_residual`,
`im05_firstStepOmitPairProductSum_eq_headWeight_residual_product`,
`im05_firstStepOmitPairProductSum_comm`,
`im05_firstStepOmitMarginalSum_eq_one_of_mem_forbidden`,
`im05_firstStepOmitPairProductSum_eq_marginal_of_left_mem_forbidden`,
`im05_firstStepOmitPairProductSum_eq_marginal_of_right_mem_forbidden`, and
`im05_firstStepOmitPairProductSum_le_mul_of_available_firstStep`.
These lemmas let a proof of the available-target first-step inequality be
promoted to the all-state form whenever an older wrapper needs that shape.
The probability-bound layer is
`im05_firstStepOmitMarginalSum_le_one`,
`im05_firstStepOmitPairProductSum_le_marginal_left`, and
`im05_firstStepOmitPairProductSum_le_marginal_right`; use these before
expanding residual laws in the averaging proof.
The weighted averaging algebra is now explicit:
`im05_weighted_opposite_spread_identity`,
`im05_weighted_product_sum_le_product_sums_of_opposite_spread_nonneg`, and
`im05_weighted_product_sum_le_product_sums_of_pairwise_opposite`.
The current exact compact first-step algebra target is therefore
`im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread_sum_nonneg`:
prove nonnegativity of the full double opposite-spread sum for the
zero-extended residual omission probabilities after each possible first head,
and the compact first-step inequality follows.  The stronger pointwise shortcut
is `im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread`, which
works if every pair of first heads has opposite movement.
For actual proof work, prefer the shorter named target
`im05_firstStepOmitPairProductSum_le_mul_of_residual_spread_sum_nonneg`; its
hypothesis is the same double-spread condition written with
`im05_firstStepHeadWeight` and `im05_firstStepResidualOmitProb`.
The shortest active first-step target is now
`0 <= im05_firstStepResidualSpreadSum ...`, consumed by
`im05_firstStepOmitPairProductSum_le_mul_of_residualSpreadSum_nonneg`.
Use `im05_firstStepResidualSpreadSum_comm` to swap targets and
`im05_firstStepResidualSpreadSum_nonneg_of_pairwise_opposite` only when every
head-pair contribution is known to be nonnegative.
The identity `im05_firstStepResidualSpreadSum_eq_two_mul_gap` and iff theorem
`im05_firstStepResidualSpreadSum_nonneg_iff` state exactly that this named
sum is twice the first-step product gap.
The zero-residual base is closed as
`im05_firstStepResidualSpreadSum_nonneg_zero_of_ne`.
The named pointwise shortcut is
`im05_firstStepOmitPairProductSum_le_mul_of_residual_pairwise_opposite`; use it
only when a local head-pair split proves each contribution nonnegative, and
otherwise stay with the summed spread target.

The compiled reductions are now layered.  The broadest version,
`im05_omissionPairNegativeCorrelation_of_tailDepth_firstStep_family`, proves
pairwise omission NC at every length from compact first-step averaging at every
successor length.  The positive-residual variant
`im05_omissionPairNegativeCorrelation_of_tailDepth_positive_firstStep_family`
uses the closed one-draw base and needs first-step averaging only when the
residual length is positive.  The intermediate two-step reduction,
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStep_firstStep_family`,
isolates the two-draw tail-depth base and needs first-step averaging only when
the residual length is at least two.  That base is now discharged by
`im05_omissionPairNegativeCorrelation_two_of_ne`, yielding
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_firstStep_family`.
The already-forbidden boundary cases are now closed by
`im05_omissionPairNegativeCorrelation_of_left_mem_forbidden` and
`im05_omissionPairNegativeCorrelation_of_right_mem_forbidden`, yielding the
tighter available-state induction theorem
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_firstStep_family`.
Use this version when attacking the remaining algebra: it only asks for the
compact first-step inequality when both targets are outside the current
forbidden set.
The residual-spread version
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_residual_spread_family`
pushes the exact named double-spread condition through that same induction, and
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_residual_spread_family`
specializes it to the source rank block.
The current paper-facing source block and Lemma 4.1 endpoints for this exact
condition are
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_residual_spread_averaging`
and
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residual_spread_and_lemma4_4`.
The even shorter Lemma 4.1 endpoint is
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residualSpreadSum_and_lemma4_4`.
The finite-weight approximation analogue is
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_residualSpreadSum_and_lemma4_4`.
The generic Algorithm 4.2 surface wrapper
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_firstStep_averaging`
uses this induction theorem for any two concrete targets with supplied
`im05_tailDepth` facts.
The available-state generic wrapper is
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_available_firstStep_averaging`.
The corresponding source-block wrappers are
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_firstStep_family`,
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_positive_firstStep_family`,
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_firstStep_family`,
and
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_firstStep_family`.
The paper-facing wrapper
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_firstStep_averaging`
turns the same compact first-step averaging input directly into the concrete
Algorithm 4.2 source-tail pairwise NC statement.
The available-state version is
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_available_firstStep_averaging`.
The wrapper
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_firstStep_averaging_and_lemma4_4`
now composes that same first-step input directly to the corrected source-range
Lemma 4.1 reciprocal bound for the full-support fresh-list law.
The sharper paper-facing endpoint
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_available_firstStep_averaging_and_lemma4_4`
does the same using only the available-state first-step family.  Thus the
remaining stochastic target in this branch is only the compact first-step
inequality family for residual lengths at least two and available distinct
targets.

Use this source-block theorem first for the actual full-support `prob` law.
Applying it to arbitrary finite approximations `weightSeq scale` is not
automatic, because the source block is ranked by `prob`; a finite-weight route
would need an additional assumption or lemma saying those prob-ranked targets
still satisfy `im05_tailDepth` for `weightSeq scale`.
With such finite-scale tail-depth facts in hand, use
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_firstStep_averaging`
rather than trying to force the source-rank specialization to rewrite across
different rankers.
The wrapper
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_firstStep_averaging_and_lemma4_4`
packages exactly that finite-scale route and composes it to the corrected
source-range Lemma 4.1 endpoint.
The available-state finite-scale variant is
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_available_firstStep_averaging_and_lemma4_4`;
use it when the finite-scale first-step algebra has been proved only for
targets outside the current forbidden set.

Prefer the rank-index Lemma 4.1 endpoints when the tail is a popularity-rank
block:

`paper_im05_lemma4_1_from_tail_negative_correlation_and_algorithm4_2_freshList_rank_indices_lemma4_3`

`paper_im05_lemma4_1_from_tail_variance_factor_and_algorithm4_2_freshList_rank_indices_lemma4_3`

`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_conditional_and_lemma4_4`

`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_multiset_limits_and_lemma4_4`

`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_weight_limits_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_firstStep_averaging_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_available_firstStep_averaging_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_pairwise_negative_correlation_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_firstStep_averaging_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_available_firstStep_averaging_and_lemma4_4`

`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`

`paper_im05_sourceRankTailBlock_freshList_conditional_from_pairwise_negative_correlation`
turns finite-scale pairwise negative correlation on the source rank block into
the finite-scale conditional comparison expected by the weight-limit wrapper.

`paper_im05_lemma4_1_from_tail_negative_correlation_and_algorithm4_2_freshList_lemma4_3`

`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`

`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`

`paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`

For a weaker but still asymptotically useful repair, the constant-factor route
is:

`paper_im05_lemma4_1_from_tail_variance_factor_and_lemma4_3`.

This changes the stochastic target from exact `Var <= E` to
`Var <= C * E`; the final constant becomes `(8C+4)` rather than `12`, but a
fixed `C` is enough for the Theorem 3.1 vanishing-fraction endpoint.

The older source-route proof algebra still knows how to lift a single-man
conditional comparison through independent men.  Its source obligation was:

`Pr[one list omits i through k | one list omits j through k] <=
 Pr[one list omits i through k]`.

The finite event-inclusion half of this argument is closed: in any permutation
sample, `k` distinct non-`j` names before the first `i` implies `k` distinct
names before the first `i`, and this inclusion lifts to a probability
inequality. The order-closed limit-passing step is also closed. The generic
fresh-list convergence half is now closed for approximating weight vectors:
pointwise convergence of weights gives convergence of all fixed fresh-list
events and, under full support of the limit, conditional omission probabilities.
The `k = 2` instance of this one-man comparison is now closed for raw integer
counts and for scaled-count limits.  The declarations
`paper_im05_lemma4_4_freshList_conditional_comparison_countWeight_two`,
`paper_im05_lemma4_4_freshList_conditional_comparison_family_from_scaled_count_negative_correlation_limits_two`,
and
`paper_im05_lemma4_4_variance_le_expectation_from_freshList_scaled_count_negative_correlation_limits_two`
are the current strongest positive endpoints.  The arbitrary-`k` extension is
not a remaining proof obligation in its current form: it is false for the
recursive fresh-list/Plackett--Luce sampler at `k = 3`.  The exact scalar
witness is recorded in
`im05_plackettLuce_k3_omission_negative_correlation_counterexample_scalar`,
`im05_plackettLuce_k3_conditional_comparison_counterexample_scalar`, and
`NegativeCorrelationCounterexample.md`.  A stronger scalar witness,
`im05_lemma4_4_variance_counterexample_scalar`, records an actual finite
variance violation for five men, five women, `k = 3`, and weights
`[50, 50, 1, 1, 1]`.

This changes the Lemma 4.4 branch from "prove the hard general
negative-dependence theorem" to "find a corrected source statement."  Viable
next moves are: restrict the theorem to a validated special case, replace the
variance proof with a weaker bound that is actually true for Plackett--Luce
top-`k` lists, or add a paper-facing validation issue and continue on
independent branches such as the Algorithm 4.1/Theorem 4.1 trace.  The current
Lean API supports the weaker-bound option through the constant-factor tail
bridge above.

There is also a concrete source-shaped model,
`im05_integerMultisetPermutationSample`, with a canonical count-vector
multiset/list construction, an automatic nonempty instance for every count
vector, and uniform permutation wrappers through
`paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_limits`
and
`paper_im05_lemma4_4_variance_le_expectation_from_freshList_integerMultiset_limits`.
There is also a pair-dependent weight-limit bridge
`paper_im05_lemma4_4_freshList_conditional_comparison_family_from_pair_weight_limits`
and a scaled integer-count bridge
`paper_im05_lemma4_4_freshList_conditional_comparison_family_from_scaled_count_weight_limits`.
The paper-facing theorem
`paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_finite_laws_and_scaled_count_limits`
now exposes the two exact finite law equalities needed from uniform
count-vector permutations and then handles the finite inclusion, positive
rescaling, and limit passage.
However, the exact conditional equality suggested by the paper's deletion
paragraph is false for nonuniform weights once `k >= 2`; conditioning on
omission of `j` from the first `k` distinct draws is not the same as deleting
`j`'s weight.  The tempting repair, an upper bound by the deleted-`j` process,
is also false already at `k = 2`: weights `i=2, j=1, a=1, b=1` give
`Pr[omit i | omit j] = 0.17647...`, while the deleted-`j` process gives
`0.16666...`.  The final negative-correlation inequality still holds in this
example, so the finite-scale route must prove the conditional comparison
directly for weighted without-replacement samples rather than routing through a
deleted-process upper bound.  The existing erased-upper-bound wrappers are
therefore conditional staging endpoints only; they are not the intended final
Lemma 4.4 proof path.
These use the reusable scaling-invariance lemmas
`finiteAvailableWeight_const_mul`,
`finiteFreshListAtomWeight_const_mul`,
`finiteWithoutReplacementPMF_event_prob_const_mul`, and
`finiteWithoutReplacementPMF_conditional_prob_const_mul`, so finite inequalities
proved for raw integer counts can be normalized by any positive scale before
passing to pointwise weight limits.
The current full-support Lemma 4.1 wrappers already discharge the positivity
side conditions for the target conditional probability.

## Lemma 4.4 Proof Plan

For the concrete fresh-list sampler, an omission event for a woman is the event
that the length-`k` weighted without-replacement list does not contain her. The
paper proves negative correlation by conditioning on one omitted woman and
arguing that another woman is no more likely to be omitted. In Lean there are
two possible routes:

1. Direct combinatorial route over `finiteFreshList`: compare atom sums for
   lists excluding `j` with atom sums excluding both `i` and `j`, using the
   recursive product formula for without-replacement weights.
2. Generic probability route: prove a reusable negative-association theorem
   for the weighted without-replacement sampler, then specialize to omission
   indicators.

The direct theorem to try first is:

`pmfConditionalProb (finiteWithoutReplacementPMF w ... k F)
  (omit j) (omit i) <= pmfProb (finiteWithoutReplacementPMF w ... k F) (omit i)`

for `i != j`, `i,j ∉ F`, full support, and `F.card + k < #α` (or the sharp
room assumptions needed for positivity). A plausible proof is an induction on
`k` using the recursive head/tail law. The key auxiliary monotonicity should be
that the hit probability of `i` weakly increases when a different atom `j` is
added to the forbidden set:

`Pr_F[hit i in k draws] <= Pr_{F∪{j}}[hit i in k draws]`.

For the induction step, compare first-draw recurrences. The algebra wants two
supporting facts:

1. hit probability is monotone in the number of remaining draws;
2. after a first draw `a`, the induction hypothesis applies to the tail state
   `F∪{a}` versus `F∪{a,j}`.

If this induction becomes too algebra-heavy in Lean, use the corrected
named-paper finite-multiset bridge: define the first-`k` distinct names of a
random multiset permutation, prove a finite upper bound from the conditional
fresh-list probability to the erased multiset event, use the already formalized
deletion/inclusion inequality, and then pass to pointwise weight limits with
the closed convergence wrappers.
The sample space side of this fallback is now in Lean: a scale is a count vector
`count : I -> Nat`, and a permutation sample is a word of length `sum count`
whose name counts match `count`; the subtype is now inhabited by the canonical
count-vector list. The marginal finite law is now closed through `k = 2`, and
the singleton-deletion projection is closed for arbitrary `k`. The next missing
bridge would have been the direct finite weighted-without-replacement
negative-dependence theorem for arbitrary `k`, but the `k = 3` counterexample
shows that this bridge is false as stated. The `k = 2` version is closed by
explicit Plackett--Luce algebra: exact two-slot atom and one-target factor
formulas, outside-sum splitting, the scalar
`im05_two_draw_hit_negative_correlation_core_prob_shape`, and complementing hit
events to omission events. For larger `k`, do not try to prove the published
one-man comparison without first changing the statement.

For the corrected branch, prefer a theorem stated directly on the chosen tail
count.  If the argument becomes reusable and clean, move the final
tail-negative-dependence or tail-variance theorem into
`EconCSLib/Foundations/Probability/WithoutReplacement.lean`. Otherwise, keep it
near the named-paper route and document the deviation from the printed Lemma
4.4.

## After Lemma 4.4

The Algorithm 4.1 output contract is now stated and proved as a certificate
surface, and strict woman preferences are enough to construct an abstract
worst-to-best stable-husband list by sorting the stable-husband set. The
shared matching library now has `daStateAfterStepsFrom`, `divorceWomanState`,
`remainingProposalCount_le_card_mul`, `no_active_daStateAfterStepsFrom_card_mul`,
`DAInvariantsExceptWoman`, the closed target-exception step-preservation and
fold wrappers, and `stable_of_stableExceptWoman_and_no_target_block`; the paper
file has named Algorithm 4.1 resumed-run and held-men-prefix wrappers, plus the
proof that the divorced starting state satisfies the target-exception invariant,
the resumed run preserves it, and the resumed run terminates by the uniform
proposal bound.  Source audit caveat: this resumed run is not yet a faithful
model of Algorithm 4.1, because `g`'s post-divorce acceptance decision should be
based on the best proposer so far, not merely on `g`'s current match. The
minimal target-standard acceptance predicate, update monotonicity lemma,
proposal-history accept/best-so-far layer, and non-target compatibility bridge
are already present; `im05_algorithm41SourceStepAccepts` is the source-shaped
acceptance predicate for the selected proposal, and
`im05_algorithm41SourceStep` is the corresponding one-step transition. The
source-history trace now has finite-run/final-state/held-men wrappers and proves
the source held-men list is nodup and ordered worst-to-best when the initial DA
run matched `g`. It also preserves the full target-exception invariant package
on all-acceptable domains and proves
`im05_algorithm41SourceFinalState_target_holder_mem_stableHusbands`, so any
source final target holder is already a stable husband.  After rechecking Step
4(b), the next proof should move from `im05_algorithm41SourceHeldMen` to the
corrected target-divorcing output list
`im05_algorithm41SourceDivorceTargetAcceptedMen`: it includes the initial DA
husband and every later target acceptance event before the immediate divorce.
That corrected list now has the core output-shape facts: target-divorcing runs
preserve the target-exception invariant package, keep `g` unmatched after every
prefix, proposal histories only shrink, later target-acceptance events cannot
repeat a man, the initial husband cannot reappear, and
`im05_algorithm41SourceDivorceTargetAcceptedMen` is nodup and ordered
worst-to-best.  The forward inclusion is now closed under all-acceptable
preferences: the initial DA husband is a stable husband, later target-acceptance
events construct a stable matching immediately before the Step 2 divorce, and
the accepted-men list is a subset of `im05_stableHusbands`.
The witness-form variants
`im05_algorithm41SourceStepTargetAccepted_stable_match_witness_of_allPairsAcceptable`
and
`im05_algorithm41SourceDivorceTargetAcceptedMen_stable_match_witness_of_allPairsAcceptable`
return an explicit stable matching with `m_match m = some g`.  The first output is
also proved to be `g`'s worst stable husband on the strict equal-size
all-acceptable domain.  The full Theorem 4.1 wrapper can now be discharged from
either the remaining backward inclusion or the weaker cardinal lower bound
`(im05_stableHusbands ... g).card <= acceptedMen.length`.

The current local backward bridge is the target-rejection exclusion lemma:
`im05_algorithm41SourceStep_target_reject_not_mem_stableHusbands_of_rejected_pair_impossible_except_target`.
It proves that a target proposer rejected by the source history rule cannot be a
stable husband, assuming proposal order, current-match order, and rejected-pair
impossibility away from the target.  The target exception is essential because
accepted target pairs are intentionally removed and can still be stable.  The
current-match-order assumption is now automatic along the corrected trace under
strict women and all-acceptable preferences; the remaining clean target is a
trace-coverage theorem showing every stable husband becomes the chosen proposer
to `g` at a prefix where the target-exception rejected-pair invariant holds.
The wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals`
then discharges the paper-facing output contract.  Be careful with rejected-pair
preservation: it is validated for target-only active prefixes, but a general
non-target step can interact with the allowed target exception and needs a
separate blocking argument.  The predicate
`im05_SourceStepNonTargetRejectedPairExclusions` names exactly those remaining
single-step exclusions, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`
is the current narrowest final wrapper.  The newest reduction shows it is enough
to prove exception-partner side conditions: the better prior proposer in a
non-target rejection, and the accepted proposer in a non-target displacement,
must not be matched to `g` in the stable matching used for contradiction.  Use
`im05_SourceTraceExceptionPartnerExclusions` as the compact prefix assumption
for this package.  If the argument naturally proves stable-husband exclusions
instead, use the step-local
`im05_SourceStepNonTargetBlockersNotStableHusbands`; the compiled
`im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers` bridge
lifts it to `im05_SourceTraceNonTargetBlockersNotStableHusbands`, and
`im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`
turns those exclusions into the compact exception-partner condition.  The
paper-facing wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`
then gives the corrected output contract.  A source-faithful variant,
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`,
only asks for target-proposal coverage through
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`, because the
initial DA husband is already in the output list before the trace loop.  Use
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_removed_target_proposals`
when the proof can show target proposal-set removal by the final source state;
the corresponding final wrapper is
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.
The strict-domain start side is no longer an assumption:
`im05_noninitial_stableHusband_mem_divorced_proposals` derives it from
women-pessimality of men-proposing DA, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`
uses only final target-removal for non-initial stable husbands.
If the final-state argument is easier as a preference statement, use
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`:
for each non-initial stable husband, prove that any final assigned woman is
strictly worse for him than `g`.
Equivalently, prove `im05_Algorithm41SourceCompletionCertificate`, whose two
fields are exactly the one-step blocker predicate and that final-match
preference condition.
The final-match preference field can be supplied through the target-blocking
predicate `im05_SourceFinalNoninitialStableHusbandTargetBlocks`, and the
current preferred wrapper is
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`.
The
old non-divorcing held-men equality should be treated only as a scaffold, not
the final paper model.

After Theorem 3.1 is assembled, move to the uniform branch. The key remaining
work is a precise Experiment 3 coupling or a corrected paper-faithful
per-index event that genuinely has probability `1 / n^2`.
