# Next-Agent Handoff: IM05 Marriage, Honesty, and Stability

This file is the starting point for the next agent.  It assumes no conversation
context.

Last refreshed: May 16, 2026.

## Stronger-Model Pause Summary

As of the May 16, 2026 DAG/status refresh, this paper is substantial but not in
cleanup mode.  The named-result infrastructure is broad, and
`lake build IM05MarriageHonestyStability` was clean at code commit `29895be`,
but the remaining obligations are still the hard paper-level proof seams.

Do not spend first tokens rediscovering status.  Start from this file, the
README `DAG Status Refresh`, `DependencyDAG.tex`, and
`FINAL_VALIDATION_REPORT.md`.  Treat helper-family details as implementation
support; the main paper-facing blockers are:

1. **Algorithm 4.1 / Theorem 4.1.**  Discharge
   `im05_Algorithm41SourcePairWitnessCompletionCertificate` for the corrected
   target-divorcing run
   `im05_algorithm41SourceDivorceTargetAcceptedMen`.  The strongest current
   one-stop paper wrapper is
   `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`.
   The certificate packages the non-target blocking-pair witness preference
   obligation and final target-removal for non-initial stable husbands.
2. **Theorem 3.1 / Lemma 4.1.**  The printed Lemma 4.4 is false for arbitrary
   nonuniform `D^k`; use the repaired rank-tail variance route.  The missing
   stochastic input is either tail negative correlation or a direct
   constant-factor tail-variance bound for the concrete Algorithm 4.2
   fresh-list law, plus the stable-market random-variable wiring.
3. **Theorem 3.2 / Section 6.**  Build the concrete five-experiment random
   process and finish the Experiment 3 redundant-pair probability reduction.

Secondary remaining work includes the Corollary 3.1-3.3 mechanism/incentive
wrappers, Appendix Lemmas A.1-A.2, and the final paper-facing
`PaperInterface.lean` / post-paper audit pass if claiming a complete
verification.

Closed or mostly closed infrastructure includes the stable matching and
multi-stable-partner definitions, Theorems A-D on the documented strict
equal-size complete-domain wrappers, Theorem 3.1 linearity/asymptotic algebra,
Algorithm 4.2 fresh-list prefix laws, Lemma 4.3 ranked-tail lower-bound
machinery, Lemma 4.4 counterexamples and corrected tail bridges, Lemma 6.3,
and the Section 6 algebra under its stated hypotheses.

## Current State

The paper is partially formalized.  The most important recent discovery is a
source validation issue in Lemma 4.4:

- The paper's arbitrary-nonuniform model draws each man's length-`k` list from
  an arbitrary positive distribution `D` by repeated independent draws with
  repetitions removed.
- Lemma 4.4 claims `Var(Y_g) <= E[Y_g]`.
- The proof reduces this to `Pr[F_i | F_j] <= Pr[F_i]` and treats conditioning
  on `F_j` as deleting woman `j` from the underlying multiset/permutation
  process.
- That conditioning/deletion step is false for nonuniform `D`.
- The unrestricted variance lemma is also false as stated.

Read first:

1. `papers/IM05MarriageHonestyStability/LEMMA4_4_COUNTEREXAMPLE_REPORT.md`
   for a standalone human-checkable counterexample.
2. `papers/IM05MarriageHonestyStability/FINAL_VALIDATION_REPORT.md` for
   current paper-level status and the proof-deviation inventory.
3. `papers/IM05MarriageHonestyStability/ProofStrategy.md` for the live proof
   plan and theorem names.
4. `papers/IM05MarriageHonestyStability/README.md` for the named-result status
   table.

## Last Verified Lean State

The last successful target build before this handoff was:

```text
lake build IM05MarriageHonestyStability
```

It completed successfully after adding the corrected tail-count Lemma 4.4 and
Lemma 4.1 bridges.

It was rebuilt successfully on May 15, 2026 after adding the source-range
pairwise-NC finite-weight endpoint, the one-head/two-head finite
without-replacement recurrences, the compact first-step sums, the generic
tail-depth induction theorem, and the source-tail first-step-family reduction.

It was rebuilt successfully again on May 15, 2026 after adding the generic
two-draw weighted-without-replacement omission NC base and the narrowed
two-step-base source-tail reduction.

It was rebuilt successfully again on May 15, 2026 after adding the
paper-facing arbitrary-real-weight `k = 2` fresh-list NC wrapper.  The latest
documentation/comment update also records an Algorithm 4.1 source-model caveat:
the current resumed-DA trace is only a scaffold because it does not store `g`'s
remembered post-divorce acceptance threshold.

It was rebuilt successfully again on May 15, 2026 after adding the
Algorithm 4.1 proposal-history accept/best-so-far layer and the non-target
current-match/history compatibility bridge described below.

It was rebuilt successfully again on May 15, 2026 after adding the
`im05_algorithm41SourceStepAccepts` chosen-proposal source acceptance seam and
the `im05_algorithm41SourceStep` one-step transition.

It was rebuilt successfully again on May 15, 2026 after closing the
source-step/ordinary-DA equivalence under full invariants, the non-target
target-exception equivalence, the ordinary-DA current-match-order bridge from
the initial DA state through the target-divorced start, and trace-level
Algorithm 4.1 backward-inclusion wrappers that package the remaining
target-proposal/rejected-pair prefix obligation.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_SourceTraceNonTargetBlockersNotStableHusbands`,
`im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`,
and the corresponding paper-facing Algorithm 4.1 output wrapper.

It was rebuilt successfully again on May 15, 2026 after adding the step-local
predicate `im05_SourceStepNonTargetBlockersNotStableHusbands`, the lift
`im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers`, and the
paper-facing wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.

It was rebuilt successfully again on May 15, 2026 after adding the
source-faithful except-initial coverage predicate
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`, the
except-initial backward-inclusion wrapper, and the final Algorithm 4.1 endpoint
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`.

It was rebuilt successfully again on May 15, 2026 after adding proposal-removal
trace extraction:
`im05_algorithm41SourceStepDivorceTarget_removed_proposal_eq_chosen`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps_removed_proposal_exists_chosen`,
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_removed_target_proposals`,
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.

It was rebuilt successfully again on May 15, 2026 after proving
`im05_noninitial_stableHusband_mem_divorced_proposals`, which closes the
start-available side of target-proposal coverage for non-initial stable
husbands on the strict equal-size all-acceptable domain, and after adding
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands`.

It was rebuilt successfully again on May 15, 2026 after adding the generic
terminal-state lemma
`im05_not_mem_proposals_of_terminated_prefers_target_to_current` and the final
Algorithm 4.1 reduction
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands`.

It was rebuilt successfully again on May 15, 2026 after adding equal-size
wrappers for the final-removal and final-preference Algorithm 4.1 endpoints,
removing the explicit initial-husband witness from those intermediate
paper-facing layers.

It was rebuilt successfully again on May 15, 2026 after adding matching
equal-size wrappers for the final-removal and final-preference trace-coverage
lemmas, so the lower `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`
route also derives the initial-husband witness internally.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_mem_stableHusbands_iff_exists_stable_exception_match`,
`im05_not_mem_stableHusbands_of_forall_stable_not_exception_match` and
`im05_not_mem_stableHusbands_iff_forall_stable_not_exception_match`, which
convert stable-husband non-membership into the all-stable-match exclusion form
and expose the direct `m_match _ = some g` membership witness form.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_SourceTraceNonTargetBlockersNotStableHusbands_iff_stepBlockers`, the
two-way bridge between the trace and per-step blocker predicates.

It was rebuilt successfully again on May 16, 2026 after adding the stronger
local stable-matching exclusion interface
`im05_SourceStepNonTargetStableMatchExclusions` and bridge
`im05_SourceStepNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`.

It was rebuilt successfully again on May 16, 2026 after adding the trace-level
stable-matching exclusion interface `im05_SourceTraceNonTargetStableMatchExclusions`
and bridge
`im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalPref`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalPref_of_card_eq`,
which package the current reduced endpoint as stable-match exclusions plus the
matched-final-assignment preference premise.

It was rebuilt successfully again on May 16, 2026 after adding the direct
trace-coverage wrappers
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceStableMatchExclusions`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepStableMatchExclusions`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetBlocks`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`,
the compact final-target-blocking version of the stable-match-exclusion endpoint.

It was rebuilt successfully again on May 16, 2026 after adding direct
stable-match-exclusion/final-target-blocking projections for backward
inclusion, accepted-men finset equality, accepted-men length equality, and
worst-to-best order.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceStepNonTargetRejectedPairExclusions_of_stableMatchExclusions`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceStableMatchExclusions`,
and
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepStableMatchExclusions_prefix`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_final_target_removed`,
`im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetRemoved`,
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetRemoved_of_card_eq`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_final_target_removed_of_SourceFinalNoninitialStableHusbandTargetBlocks`
and
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_final_target_removed`.

It was rebuilt successfully again on May 16, 2026 after adding the target-only
prefix special case
`im05_SourceTraceNonTargetStableMatchExclusions_of_target_chosen_prefix` and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_target_chosen_prefix`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceStepNonTargetBlockingPreferences` and
`im05_SourceStepNonTargetRejectedPairExclusions_of_blockingPreferences`, a
direct blocking-inequality route for non-target rejected/displaced pairs.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceTraceNonTargetBlockingPreferences`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceBlockingPreferences`,
and the paper-facing wrappers ending in `_of_traceBlockingPreferences` and
`_of_stepBlockingPreferences`.

It was rebuilt successfully again on May 16, 2026 after adding
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_traceBlockingPreferences`,
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepBlockingPreferences`,
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepBlockingPreferences_of_card_eq`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceStepNonTargetBlockingPairPreferences` and
`im05_SourceStepNonTargetRejectedPairExclusions_of_blockingPairPreferences`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceTraceNonTargetBlockingPairPreferences`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceBlockingPairPreferences`,
and paper-facing wrappers ending in `_of_stepBlockingPairPreferences` and
`_final_target_removed_of_stepBlockingPairPreferences_of_card_eq`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_active_proposer_prefers_chosen_in_stable_match_except_exception`,
`im05_SourceStepNonTargetBlockingPairPreferences_of_stableMatchExclusions`,
and
`im05_SourceTraceNonTargetBlockingPairPreferences_of_stableMatchExclusions`,
which show that the stronger stable-match-exclusion route also supplies the
sharper pair-level blocking-preference route.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_SourceStepNonTargetBlockingPairPreferences_of_blockingPreferences` and
`im05_SourceTraceNonTargetBlockingPairPreferences_of_blockingPreferences`,
which coerce the broader direct blocking-preference predicate into the sharper
pair-level route.

It was rebuilt successfully again on May 16, 2026 after adding the full
target-proposal paper wrappers
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceBlockingPairPreferences`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepBlockingPairPreferences`.

It was rebuilt successfully again on May 16, 2026 after adding direct
pair-level final-removal projection lemmas for backward inclusion, accepted-men
finset equality, accepted-men length equality, and worst-to-best order; their
names end in `_of_stepBlockingPairPreferences_finalTargetRemoved_of_card_eq`.

It was rebuilt successfully again on May 16, 2026 after adding the analogous
broad blocking-preference final-removal projection lemmas, whose names end in
`_of_stepBlockingPreferences_finalTargetRemoved_of_card_eq`.

It was rebuilt successfully again on May 16, 2026 after adding the compact
preferred remaining-obligation certificate
`im05_Algorithm41SourcePairCompletionCertificate`, the one-stop paper wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairCompletionCertificate_of_card_eq`,
and its direct accepted-men finset projection.

It was rebuilt successfully again on May 16, 2026 after adding the weaker
rejection-side witness route
`im05_SourceStepNonTargetBlockingPairWitnessPreferences`, its trace predicate,
rejected-pair preservation wrappers, and paper-facing full-target,
except-initial, and final-removal endpoints ending in
`BlockingPairWitnessPreferences`.

It was rebuilt successfully again on May 16, 2026 after adding the compact
witness-form remaining-obligation certificate
`im05_Algorithm41SourcePairWitnessCompletionCertificate`, its one-stop
paper-facing wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`,
and its accepted-men finset projection.

It was rebuilt successfully again on May 15, 2026 after adding the bundled
remaining-obligation target `im05_Algorithm41SourceCompletionCertificate` and
the one-stop paper-facing wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate`.

It was rebuilt successfully again on May 15, 2026 after adding the final
target-blocking bridge
`im05_SourceFinalNoninitialStableHusbandTargetBlocks`,
`im05_SourceFinalNoninitialStableHusbandTargetBlocks.finalPref`,
`im05_Algorithm41SourceCompletionCertificate_of_finalTargetBlocks`, and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks`.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_Algorithm41SourceCompletionCertificate_of_finalPref`, which packages the
matched-final-assignment preference premise directly into the source completion
certificate under all-acceptable preferences.

It was rebuilt successfully again on May 16, 2026 after adding
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalPref_of_card_eq`,
the one-stop paper-facing wrapper from the matched-final-assignment preference
premise.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_finalPref` and
`im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_finalPref`, which
make the `valM` unmatched case automatic under all-acceptable preferences and
reduce the target-blocking proof to the matched-final-assignment preference
obligation.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_finalTargetBlocks_of_card_eq`,
which sends the final-target-blocking predicate directly to the except-initial
target-proposal coverage predicate under equal cardinality.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`,
a direct backward-inclusion corollary from the current final-target-blocks
endpoint.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_finalTargetBlocks_of_card_eq`,
the direct finset equality projection from the same endpoint.

It was rebuilt successfully again on May 15, 2026 after adding
`im05_algorithm41SourceDivorceTargetAcceptedMen_length_eq_stableHusbands_card_of_finalTargetBlocks_of_card_eq`,
the direct length/cardinality equality projection from the same endpoint.

It was rebuilt successfully again on May 16, 2026 after adding
`im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest_of_finalTargetBlocks_of_card_eq`,
the direct worst-to-best order projection from the same endpoint.

It was rebuilt successfully again on May 15, 2026 after adding the equal-size
paper-facing wrappers
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate_of_card_eq`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`,
which derive the initial-husband witness internally from equal cardinality and
all-acceptable preferences.

It was rebuilt successfully again on May 15, 2026 after adding
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_firstStep_averaging_and_lemma4_4`,
which composes the compact first-step averaging family directly to the
corrected source-range Lemma 4.1 reciprocal bound for the concrete full-support
fresh-list law.

It was rebuilt successfully again on May 15, 2026 after adding the generic
Algorithm 4.2 wrapper
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_firstStep_averaging`,
which proves pairwise omission NC from target-specific `im05_tailDepth` facts
plus the compact first-step averaging family.

It was rebuilt successfully again on May 15, 2026 after adding
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_firstStep_averaging_and_lemma4_4`,
which composes finite-scale `im05_tailDepth` facts plus first-step averaging
through the weight-limit route to the corrected source-range Lemma 4.1 bound.

It was rebuilt successfully again on May 15, 2026 after adding the
already-forbidden boundary lemmas
`im05_omissionPairNegativeCorrelation_of_left_mem_forbidden` and
`im05_omissionPairNegativeCorrelation_of_right_mem_forbidden`, the
available-state induction wrappers
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_firstStep_family`,
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_firstStep_family`,
`im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_available_firstStep_averaging`,
and the paper-facing source-range wrapper
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_available_firstStep_averaging_and_lemma4_4`.
These reduce the hard first-step averaging obligation to residual lengths at
least two in states where both targets are still available.

It was rebuilt successfully again on May 15, 2026 after adding the matching
finite-weight approximation endpoint
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_available_firstStep_averaging_and_lemma4_4`.
This is the preferred weight-limit wrapper when the finite-scale first-step
algebra is proved only for targets outside the current forbidden set.

It was rebuilt successfully again on May 15, 2026 after adding compact
first-step boundary algebra:
`im05_firstStepOmitPairProductSum_comm`,
`im05_firstStepOmitMarginalSum_eq_one_of_mem_forbidden`,
`im05_firstStepOmitPairProductSum_eq_marginal_of_left_mem_forbidden`,
`im05_firstStepOmitPairProductSum_eq_marginal_of_right_mem_forbidden`, and
`im05_firstStepOmitPairProductSum_le_mul_of_available_firstStep`.
These are useful when an older all-state first-step wrapper must consume a
proof that has only been established for available targets.

It was rebuilt successfully again on May 15, 2026 after adding the compact
first-step probability bounds
`im05_firstStepOmitMarginalSum_le_one`,
`im05_firstStepOmitPairProductSum_le_marginal_left`, and
`im05_firstStepOmitPairProductSum_le_marginal_right`.
These keep later averaging work at the named-sum layer without re-expanding the
recursive sampler.

It was rebuilt successfully again on May 15, 2026 after adding weighted
opposite-spread averaging algebra:
`im05_weighted_opposite_spread_identity`,
`im05_weighted_product_sum_le_product_sums_of_opposite_spread_nonneg`,
`im05_weighted_product_sum_le_product_sums_of_pairwise_opposite`, and the
summed first-step specialization
`im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread_sum_nonneg`,
plus the stronger pointwise first-step specialization
`im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread`.
The next hard stochastic target can now be stated as nonnegativity of the
double opposite-spread sum for the zero-extended residual omission
probabilities across possible first heads.  Pairwise opposite movement is a
sufficient shortcut but may be stronger than needed.

It was rebuilt successfully again on May 15, 2026 after adding the named
compact first-step API
`im05_firstStepHeadWeight`, `im05_firstStepResidualOmitProb`,
`im05_firstStepResidualSpreadSum`,
`im05_firstStepResidualSpreadSum_comm`,
`im05_firstStepResidualSpreadSum_nonneg_of_pairwise_opposite`,
`im05_firstStepResidualSpreadSum_eq_two_mul_gap`,
`im05_firstStepResidualSpreadSum_nonneg_iff`,
`im05_firstStepResidualSpreadSum_nonneg_zero_of_ne`,
`im05_firstStepHeadWeight_sum_eq_one`,
`im05_firstStepHeadWeight_nonneg`, `im05_firstStepHeadWeight_le_one`,
`im05_firstStepResidualOmitProb_eq_zero_of_head_eq`,
`im05_firstStepResidualOmitProb_eq_prob_of_head_ne`,
`im05_firstStepResidualOmitProb_nonneg`,
`im05_firstStepResidualOmitProb_le_one`,
`im05_firstStepOmitMarginalSum_eq_headWeight_residual`,
`im05_firstStepOmitPairProductSum_eq_headWeight_residual_product`, and
`im05_firstStepOmitPairProductSum_le_mul_of_residual_spread_sum_nonneg`.
The short first-step theorem is
`im05_firstStepOmitPairProductSum_le_mul_of_residualSpreadSum_nonneg`.
The pointwise sufficient condition is also packaged as
`im05_firstStepOmitPairProductSum_le_mul_of_residual_pairwise_opposite`.
Use this shorter residual-spread wrapper as the next Lean target.  The exact
condition now also feeds the induction directly through
`im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_residual_spread_family`
and the source rank-block specialization
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_residual_spread_family`.
The paper-facing wrappers are
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_residual_spread_averaging`
and
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residual_spread_and_lemma4_4`.
The shortest current Lemma 4.1 endpoint is
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residualSpreadSum_and_lemma4_4`.
The finite-weight approximation analogue is
`paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_residualSpreadSum_and_lemma4_4`.

Recent Lean additions include
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_firstStep_averaging`
and
`paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_available_firstStep_averaging`,
which expose the current stochastic reductions as paper-facing Algorithm 4.2
source-tail pairwise-NC wrappers, and the Algorithm 4.1 proposal-history
accept/best-so-far layer listed next.

For Algorithm 4.1, the first minimal threshold primitives are now in
`MainTheorems.lean`: `im05_algorithm41TargetAccepts`,
`im05_algorithm41TargetStandardAfterAccept`, and
`im05_algorithm41TargetStandard_value_mono_of_accepts`.  The source
proposal-history rule is also now represented by
`im05_algorithm41HasProposedTo`, `im05_algorithm41HistoryAccepts`,
`im05_algorithm41BestProposedSoFar`,
`im05_algorithm41BestProposedSoFar_after_history_accept`, and
`im05_algorithm41HistoryAccepts_of_bestProposedSoFar_of_targetAccepts`.  The
non-target compatibility bridge is
`im05_algorithm41HistoryAccepts_of_womanRejectionInvariantExcept_current_lt`.
The chosen-proposal source acceptance seam is
`im05_algorithm41SourceStepAccepts`, with wrappers
`im05_algorithm41SourceStepAccepts_of_bestProposedSoFar_of_targetAccepts` and
`im05_algorithm41SourceStepAccepts_of_nonTarget_current_lt`.  The source-shaped
one-step transition is `im05_algorithm41SourceStep`, with proposal-history
progress lemmas `im05_algorithm41SourceStep_m_proposals_chosen` and
`im05_algorithm41SourceStep_records_chosen_proposal`.  The source accept test
now agrees with ordinary DA under full invariants via
`im05_algorithm41SourceStepAccepts_iff_daStepChosenAccepts_of_invariants`, and
away from the target under target-exception invariants via
`im05_algorithm41SourceStepAccepts_iff_daStepChosenAccepts_of_invariantsExceptWoman_nonTarget`;
the corresponding step-equality bridges are
`im05_algorithm41SourceStep_eq_daStep_of_invariants` and
`im05_algorithm41SourceStep_eq_daStep_of_invariantsExceptWoman_nonTarget`.
Source-run wrappers are now present as `im05_algorithm41SourceStateAfterSteps`,
`im05_algorithm41SourceFinalState`, `im05_algorithm41SourceHeldMenPrefix`, and
`im05_algorithm41SourceHeldMen`.  The current source trace also proves
source-step preservation of the full target-exception invariant package on
all-acceptable domains, source-final stable-except-target semantics, preservation
that any current target holder is best-so-far, preservation of a nonnegative
target best-so-far proposer from the initial DA match, target held-value
monotonicity along the source run, and
`im05_algorithm41SourceFinalState_target_holder_mem_stableHusbands`, proving any
source final target holder is a stable husband.  The wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceHeldMen_membership` remains the
source-held-men output certificate once the set equality with stable husbands is
proved.  However, after rechecking Step 4(b), the non-divorcing source-held-men
trace is only a scaffold: when `w = g` accepts, the paper immediately outputs
that man and divorces him in Step 2.  The corrected target-divorcing trace is
now present as `im05_algorithm41SourceStepTargetAccepted`,
`im05_algorithm41SourceStepDivorceTarget`,
`im05_algorithm41SourceDivorceTargetStateAfterSteps`,
`im05_algorithm41SourceDivorceTargetFinalState`, and
`im05_algorithm41SourceDivorceTargetAcceptedMen`, with finite termination
proved by `im05_algorithm41SourceDivorceTargetFinalState_terminated`.

The exact scalar counterexamples currently in Lean are:

- `im05_plackettLuce_k3_omission_negative_correlation_counterexample_scalar`
- `im05_plackettLuce_k3_conditional_comparison_counterexample_scalar`
- `im05_lemma4_4_variance_counterexample_scalar`

The corrected tail bridges currently in Lean are:

- `paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`
- `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`
- `paper_im05_lemma4_3_tail_expected_absent_count_lower_bound_from_algorithm4_2_freshList_ranked_tails_prefix_sets_product_of_top_prefix_mass`
- `paper_im05_lemma4_3_tail_expected_absent_count_lower_bound_from_algorithm4_2_freshList_rank_indices_prefix_sets_product_of_top_prefix_mass`
- `paper_im05_lemma4_1_from_tail_negative_correlation_and_algorithm4_2_freshList_rank_indices_lemma4_3`
- `paper_im05_lemma4_1_from_tail_variance_factor_and_algorithm4_2_freshList_rank_indices_lemma4_3`
- `paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_conditional_and_lemma4_4`
- `paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_multiset_limits_and_lemma4_4`
- `paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_rank_indices_full_support_weight_limits_and_lemma4_4`
- `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`
- `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`
- `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_pairwise_negative_correlation_and_lemma4_4`
- `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`
- `paper_im05_sourceRankTailBlock_freshList_conditional_from_pairwise_negative_correlation`
- `paper_im05_lemma4_1_from_tail_negative_correlation_and_algorithm4_2_freshList_lemma4_3`
- `paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_conditional_and_lemma4_4`
- `paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4`
- `paper_im05_lemma4_1_from_tail_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4`
- `paper_im05_lemma4_1_from_tail_variance_factor_and_lemma4_3`
- `im05_rankIndexBlock`, `im05_rankIndexBlock_card`,
  `im05_rankIndexBlock_start_le`, `im05_rankIndexBlock_lt_end`,
  `im05_rankIndexBlock_card_real`, `im05_rankIndexBlock_card_ge_half`,
  `im05_rankIndexBlock_half_le_rank`,
  `im05_rankIndexBlock_two_mul_k_lt_rank`,
  `im05_rankIndexBlock_tail_conditions`,
  `im05_rankIndexBlock_target_mem_lowerRankFinset_of_end_le`,
  `im05_rankIndexBlock_filter_card_le_lowerRankFinset_filter_card`,
  `im05_sourceRankTailBlock`,
  `im05_sourceRankTailBlock_tail_conditions`,
  `im05_sourceRankTailBlock_filter_card_le_lowerRankFinset_filter_card`,
  `im05_listPrefixOmits_finCons_succ_iff`,
  `im05_finiteWithoutReplacementPMF_listPrefixOmits_succ_prob_eq_sum_head`,
  `im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_prob_eq_sum_head`,
  `im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_negative_correlation_from_first_step`,
  `im05_sourceRankTailBlock_after_one_delete_tail_condition`,
  `im05_sourceRankTailBlock_priorIndexSet_erase_card_ge_two_mul_pred`,
  `im05_rankAgentByValue_prob_antitone_of_lt`

## Recommended Next Step

Do not try to prove the paper's Lemma 4.4 as printed.  It is false.

The current repair replaces `Y_g` by a tail count that matches the part of
Lemma 4.3 actually used in the expectation lower bound.  The source proof of
Lemma 4.3 lower-bounds `E[Y_g]` by summing over ranks roughly from `g/2` to
`g`, after deriving bounds valid for `w > 2k`.  Small numeric checks suggest
the negative-dependence obstruction is concentrated in the top block, not in
the tail; see `TailVarianceExploration.md` for the scratch search record.  The
generic tail-count variance and Lemma 4.1 bridges, plus concrete Algorithm 4.2
tail wrappers, are already formalized; what remains is the concrete stochastic
input for the chosen tail.

Concrete suggested target:

1. Instantiate the `tail : Finset I` argument of
   `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3` with ranks
   such as `{w : 2k < rank(w) and rank(w) <= g}` or the source's final
   `{g/2 <= rank(w) <= g}` range.
2. Prove its expectation lower bound using the existing Lemma 4.3 ranked-tail
   machinery. For contiguous `Fin N` rank blocks, use
   `im05_rankIndexBlock_tail_conditions` to discharge `hcard`, `hhalf`, and
   `htwo_k`.  If the available `X_mu(g)` domination is stated for the full
   lower-rank prefix, use
   `im05_rankIndexBlock_filter_card_le_lowerRankFinset_filter_card` to bound
   the tail count by that lower-rank count, then feed the block to the
   rank-index Lemma 4.1 wrappers above.  For the paper's final range, prefer
   `im05_sourceRankTailBlock`; it is the block of zero-based ranks
   `g / 2, ..., g - 1`, and `im05_sourceRankTailBlock_tail_conditions` packages
   the arithmetic from `g > 4k`.
3. Prove or test pairwise negative correlation, or a direct constant-factor
   variance bound `Var(Y_tail) <= C * E[Y_tail]`, for that tail count under the
   concrete Algorithm 4.2 fresh-list law.  For finite approximations,
   `paper_im05_sourceRankTailBlock_freshList_conditional_from_pairwise_negative_correlation`
   converts source-tail pairwise NC into the conditional inequality used by the
   source-range weight-limit wrapper, and
   `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_pairwise_negative_correlation_and_lemma4_4`
   composes that input all the way to the Lemma 4.1 source-range endpoint.
   The finite induction scaffolding is now:
   `im05_listPrefixOmits_finCons_succ_iff`,
   `im05_finiteWithoutReplacementPMF_listPrefixOmits_succ_prob_eq_sum_head`,
   `im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_prob_eq_sum_head`,
   `im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_negative_correlation_from_first_step`,
   `im05_firstStepOmitMarginalSum`, `im05_firstStepOmitPairProductSum`,
   `im05_firstStepOmitMarginalSum_eq_prob`,
   `im05_firstStepOmitMarginalSum_nonneg`,
   `im05_firstStepOmitPairProductSum_nonneg`,
   `im05_omissionPairNegativeCorrelation`, `im05_tailDepth`,
   `im05_tailDepth_after_insert_of_tailDepth_succ`,
   `im05_sourceRankTailBlock_tailDepth`,
   `im05_omissionPairNegativeCorrelation_of_tailDepth_firstStep_family`,
   `im05_omissionPairNegativeCorrelation_of_tailDepth_positive_firstStep_family`,
   `im05_omissionPairNegativeCorrelation_of_tailDepth_twoStep_firstStep_family`,
   `im05_omissionPairNegativeCorrelation_two_of_ne`,
   `im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_firstStep_family`,
   `im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_firstStep_averaging`,
   `im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_firstStep_family`,
   `im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_positive_firstStep_family`,
   and
   `im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_firstStep_family`.
   Use
   `paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_firstStep_averaging`
   when you want the same reduction stated directly over the concrete
   Algorithm 4.2 fresh-list PMF.
   Use
   `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_firstStep_averaging_and_lemma4_4`
   when you want that first-step input composed all the way to the corrected
   source-range Lemma 4.1 reciprocal bound.
   Use
   `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_firstStep_averaging_and_lemma4_4`
   for the finite-approximation version, where the prob-ranked targets have
   explicit tail-depth facts at each finite scale.
   The generic two-draw base is now closed; the current strongest reduced
   target is the compact first-step averaging inequality family only for
   residual lengths at least two.
4. Reuse
   `paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`
   and `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`, or
   use `paper_im05_lemma4_1_from_tail_variance_factor_and_lemma4_3` if the
   available proof gives only a fixed variance factor.
5. Record this as a proof-strategy deviation from the paper, not as a proof of
   Lemma 4.4 as stated.

If the tail variance bound fails too, stop and report the exact counterexample.

## Other Viable Branches

Algorithm 4.1 / Theorem 4.1 is independent of the Lemma 4.4 issue and remains
a good next branch, but do not treat the current resumed `DAState` wrappers as
a complete source model.  The paper's Algorithm 4.1 has `g` compare each suitor
to the best man who has proposed to her so far after divorce; the current
scaffold divorces `g` and preserves proposal histories but the resumed `daStep`
still compares against current matches.  Use the new
`im05_algorithm41HistoryAccepts` / `im05_algorithm41BestProposedSoFar` layer
and the `im05_algorithm41SourceStepAccepts` chosen-proposal seam before proving
the held-men/stable-husbands equality as the paper's trace theorem.  Start from
the minimal target-standard and proposal-history predicates listed above; the
first source-shaped step definition is already present as
`im05_algorithm41SourceStep`.

Closed infrastructure includes:

- arbitrary-start DA run: `daStateAfterStepsFrom`;
- target divorce state: `divorceWomanState`;
- target-exception invariants:
  `WomanRejectionInvariantExcept`, `DAInvariantsExceptWoman`;
- resumed-run termination and stable-except-target semantics;
- stable-except-target bridge:
  `stable_of_stableExceptWoman_and_no_target_block`;
- IM05 final-state and held-men wrappers:
  `im05_algorithm41FinalState`, `im05_algorithm41HeldMen`;
- source proposal-history primitives:
  `im05_algorithm41HasProposedTo`, `im05_algorithm41HistoryAccepts`,
  `im05_algorithm41BestProposedSoFar`;
- current-match/history compatibility away from the target:
  `im05_algorithm41HistoryAccepts_of_womanRejectionInvariantExcept_current_lt`;
- chosen-proposal source acceptance seam:
  `im05_algorithm41SourceStepAccepts`;
- source-shaped one-step transition:
  `im05_algorithm41SourceStep`;
- finite source-shaped trace and output wrappers:
  `im05_algorithm41SourceStateAfterSteps`, `im05_algorithm41SourceFinalState`,
  `im05_algorithm41SourceHeldMen`, and
  `paper_im05_theorem4_1_from_algorithm41_sourceHeldMen_membership`;
- corrected target-divorcing source trace and event-output wrappers:
  `im05_algorithm41SourceStepTargetAccepted`,
  `im05_algorithm41SourceStepDivorceTarget`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps`,
  `im05_algorithm41SourceDivorceTargetFinalState`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen`, and
  `im05_algorithm41SourceDivorceTargetFinalState_terminated`;
- corrected accepted-men output shape:
  `im05_algorithm41SourceStepDivorceTarget_preserves_invariantsExceptWoman_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetFinalState_stable_except_target_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetFinalState_w_match_target_none`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_m_proposals_subset_of_le`,
  `im05_algorithm41SourceStepTargetAccepted_ne_of_lt`,
  `im05_algorithm41InitialHusband_ne_sourceStepTargetAccepted`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_nodup`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest`, and
  `im05_algorithm41SourceDivorceTargetAcceptedMen_forward_of_allPairsAcceptable`,
  `im05_algorithm41SourceStepTargetAccepted_stable_match_witness_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_stable_match_witness_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_subset_stableHusbands_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_length_le_stableHusbands_card_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_allPairsAcceptable_card_le`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_membership`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_backward`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals`,
  and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_card_lower`;
- Algorithm 4.1 base/rejection bridges:
  `paper_im05_theorem4_1_base_case_worst_stable_husband`,
  `im05_ManCurrentMatchOrderInvariant`,
  `im05_DARejectedPairImpossibleExceptWoman`,
  `im05_deferredAcceptanceState_currentMatchOrder_of_allPairsAcceptable`,
  `im05_algorithm41DivorcedState_currentMatchOrder_of_allPairsAcceptable`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_currentMatchOrder_of_allPairsAcceptable`,
  `im05_algorithm41SourceStepDivorceTarget_preserves_currentMatchOrder`,
  `im05_algorithm41SourceDivorceTargetStateAfterStepsFrom_preserves_currentMatchOrder`,
  `im05_algorithm41SourceStep_target_reject_not_mem_stableHusbands_of_rejected_pair_impossible_except_target`,
  `im05_stableHusband_target_proposal_mem_sourceDivorceTargetAcceptedMen_of_trace_rejected_package_of_allPairsAcceptable`,
  `im05_stableHusband_initial_target_proposal_mem_sourceDivorceTargetAcceptedMen`,
  `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_trace_target_proposals`,
  `im05_SourceStepNonTargetRejectedPairExclusions`,
  `im05_SourceStepNonTargetRejectedPairExclusions_of_full_rejectedPairImpossible`,
  `im05_algorithm41SourceStepDivorceTarget_preserves_rejectedPairImpossibleExceptWoman_of_stepNonTargetExclusions`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepNonTargetExclusions_prefix`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`,
  `im05_prior_proposer_prefers_woman_in_stable_match_except_exception`,
  `im05_accepted_proposer_blocks_displaced_match_except_exception`,
  `im05_history_reject_not_mem_stableHusbands_of_rejected_pair_impossible_except_exception`,
  `im05_algorithm41SourceStep_nonTarget_reject_exclusion_of_prior_not_exception`,
  `im05_algorithm41SourceStep_nonTarget_accept_displaced_exclusion_of_proposer_not_exception`,
  `im05_SourceStepNonTargetRejectedPairExclusions_of_exception_partner_exclusions`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_exception_partner_exclusions_prefix`,
  `im05_SourceTraceExceptionPartnerExclusions`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceExceptionPartnerExclusions`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceExceptionPartnerExclusions`,
  `im05_SourceStepNonTargetBlockersNotStableHusbands`,
  `im05_SourceTraceNonTargetBlockersNotStableHusbands`,
  `im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers`,
  `im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_nonTargetBlockersNotStableHusbands`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`,
  `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_trace_target_proposals_except_initial`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`,
  `im05_algorithm41SourceStepDivorceTarget_removed_proposal_eq_chosen`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_removed_proposal_exists_chosen`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_removed_target_proposals`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`,
  `im05_noninitial_stableHusband_mem_divorced_proposals`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_target_removed`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_target_removed_of_card_eq`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`,
  `im05_not_mem_proposals_of_terminated_prefers_target_to_current`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_prefers_target_to_current`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_final_prefers_target_to_current_of_card_eq`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`,
  `im05_mem_stableHusbands_iff_exists_stable_exception_match`,
  `im05_not_mem_stableHusbands_of_forall_stable_not_exception_match`,
  `im05_not_mem_stableHusbands_iff_forall_stable_not_exception_match`,
  `im05_SourceTraceNonTargetBlockersNotStableHusbands_iff_stepBlockers`,
  `im05_SourceStepNonTargetStableMatchExclusions`,
  `im05_SourceStepNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`,
  `im05_SourceStepNonTargetRejectedPairExclusions_of_stableMatchExclusions`,
  `im05_SourceStepNonTargetBlockingPreferences`,
  `im05_SourceStepNonTargetRejectedPairExclusions_of_blockingPreferences`,
  `im05_SourceStepNonTargetBlockingPairPreferences`,
  `im05_SourceStepNonTargetRejectedPairExclusions_of_blockingPairPreferences`,
  `im05_SourceTraceNonTargetBlockingPairPreferences`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceBlockingPairPreferences`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepBlockingPairPreferences_prefix`,
  `im05_SourceTraceNonTargetBlockingPreferences`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceBlockingPreferences`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepBlockingPreferences_prefix`,
  `im05_SourceTraceNonTargetStableMatchExclusions`,
  `im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stableMatchExclusions`,
  `im05_SourceStepNonTargetStableMatchExclusions_of_target_chosen`,
  `im05_SourceTraceNonTargetStableMatchExclusions_of_target_chosen_prefix`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_traceStableMatchExclusions`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepStableMatchExclusions_prefix`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceStableMatchExclusions`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepStableMatchExclusions`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_target_chosen_prefix`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceBlockingPreferences`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepBlockingPreferences`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_traceBlockingPreferences`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepBlockingPreferences`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepBlockingPreferences_of_card_eq`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_traceBlockingPairPreferences`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepBlockingPairPreferences`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepBlockingPairPreferences_of_card_eq`,
  `im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalPref`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalPref_of_card_eq`,
  `im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetBlocks`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`,
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_final_target_removed`,
  `im05_final_target_removed_of_SourceFinalNoninitialStableHusbandTargetBlocks`,
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_final_target_removed`,
  `im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetRemoved`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetRemoved_of_card_eq`,
  `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_length_eq_stableHusbands_card_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`,
  `im05_Algorithm41SourceCompletionCertificate`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate_of_card_eq`,
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks`,
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks.finalPref`,
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_finalPref`,
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_finalPref`,
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_finalTargetBlocks_of_card_eq`,
  `im05_Algorithm41SourceCompletionCertificate_of_finalTargetBlocks`,
  `im05_Algorithm41SourceCompletionCertificate_of_finalPref`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalPref_of_card_eq`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks`,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`,
  `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_finalTargetBlocks_of_card_eq`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_length_eq_stableHusbands_card_of_finalTargetBlocks_of_card_eq`,
  `im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest_of_finalTargetBlocks_of_card_eq`,
  and
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_target_chosen_prefix`;
- source target-exception invariant preservation:
  `im05_algorithm41SourceStep_preserves_invariantsExceptWoman_of_allPairsAcceptable`,
  `im05_algorithm41SourceFinalState_satisfies_invariants_except_target_of_allPairsAcceptable`,
  and `im05_algorithm41SourceFinalState_stable_except_target_of_allPairsAcceptable`;
- source target-standard preservation and ordering:
  `im05_algorithm41DivorcedState_bestProposedSoFar_of_initial_match`,
  `im05_algorithm41SourceStep_preserves_target_nonneg_bestProposedSoFar`,
  `im05_algorithm41SourceFinalState_target_match_bestProposedSoFar`,
  `im05_algorithm41SourceStateAfterSteps_target_value_mono_of_initial_match`,
  and `im05_algorithm41SourceHeldMen_worstToBest_of_initial_match`;
- source final-holder stable-husband bridge:
  `im05_algorithm41SourceFinalState_target_holder_mem_stableHusbands`;
- target-holder membership bridge:
  `im05_algorithm41FinalState_target_holder_mem_stableHusbands_of_no_target_block`;
- held-men list nodup/order and output certificate wrappers.

The remaining hard bridge should now be stated for the corrected
`im05_algorithm41SourceDivorceTargetAcceptedMen` event-output list, not the
older non-divorcing `im05_algorithm41SourceHeldMen` scaffold.  Its nodup,
worst-to-best, and forward-inclusion facts are closed; prove that its set is
exactly `im05_stableHusbands`.  Equivalently, prove the pointwise backward
inclusion in
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_backward`,
or prove the weaker cardinal lower bound consumed by
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_card_lower`.
The promising local route is to preserve the target-exception rejected-pair
impossibility invariant through the corrected trace, then apply the closed
target-rejection lemma to show a stable husband cannot be rejected by `g`.
That preservation is now closed for prefixes whose active steps all choose the
target, but the general non-target-step case is the hard point: a displaced
non-target pair can interact with the allowed target exception, so do not assume
the full target-exception rejected-pair invariant pushes through every
non-target source step without an additional argument.  The remaining hard case
is now isolated by `im05_SourceStepNonTargetRejectedPairExclusions`: prove those
per-step exclusions and the stable-husband target-proposal coverage, then
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`
discharges the corrected Theorem 4.1 output contract.
The per-step exclusions are further reduced to exception-partner side
conditions: prove that the prior/chosen proposer used to block a non-target
rejection or displacement is not matched to `g` in the candidate stable
matching, then
`im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_exception_partner_exclusions_prefix`
recovers the rejected-pair package along the prefix.
The readable final conditional endpoint is now
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceExceptionPartnerExclusions`:
provide `im05_SourceTraceExceptionPartnerExclusions` up to the finite horizon
and target-proposal coverage for every stable husband.
There is also a cleaner stable-husband-set side-condition endpoint:
`im05_SourceStepNonTargetBlockersNotStableHusbands` is the one-step local
target, `im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers`
lifts it to `im05_SourceTraceNonTargetBlockersNotStableHusbands`, and the trace
predicate implies the compact exception-partner predicate through
`im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`,
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`
uses that condition plus target-proposal coverage to prove the same corrected
output contract.
Prefer the source-faithful endpoint
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`:
its coverage input is
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`, so it does
not ask the initial DA husband to propose to `g` again after being output and
divorced.
The coverage condition can now be reduced further to final proposal-set
removal: prove that each non-initial stable husband has `g` in his proposal set
at `im05_algorithm41DivorcedState` and no longer has `g` in his proposal set at
`im05_algorithm41SourceDivorceTargetFinalState`, then
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`
composes that with the one-step blocker exclusions.
The first half of that removal premise is now automatic:
`im05_noninitial_stableHusband_mem_divorced_proposals` proves that every
non-initial stable husband starts with `g` available in the divorced state.
The current strongest wrapper is therefore
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`;
prove its `hfinalRemoved` premise and the one-step blocker predicate.
Equivalently, use
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`
and prove that each non-initial stable husband strictly prefers `g` to any
woman he is matched with in the corrected final state.
The shortest current target is `im05_Algorithm41SourceCompletionCertificate`;
its two fields are exactly that final-match preference condition and the
one-step non-target blocker package.
The final-match field can now be supplied through the cleaner target-blocking
predicate `im05_SourceFinalNoninitialStableHusbandTargetBlocks`; the wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`
is the current preferred paper-facing endpoint.
The old final-source-holder bridge is still useful as a local blocking-pair
pattern, but the final paper-facing Theorem 4.1 should be routed through the
target-divorcing output list.

Theorem 3.2 / Section 6 is another independent branch.  Lemma 6.3 and much of
the five-experiment algebra are formalized, but Experiment 3's source-faithful
per-pair probability argument remains open.

## Files Changed in This Handoff

Key files updated for this handoff:

- `skills/econcs-formalizer/references/proof-markets-social-choice.md`: holds
  the IM05-specific lessons about false conditioning/deletion arguments, the
  variance-level counterexample, and the tail-count repair direction.
- `papers/IM05MarriageHonestyStability/LEMMA4_4_COUNTEREXAMPLE_REPORT.md`:
  standalone counterexample report for humans.
- `papers/IM05MarriageHonestyStability/FINAL_VALIDATION_REPORT.md`:
  paper-level validation status and deviation record.
- `papers/IM05MarriageHonestyStability/NEXT_AGENT_HANDOFF.md`:
  this file.
- `EconCSLib/Foundations/Probability/Weighted.lean`: reusable available-mass
  insert/subtraction and positive-atom lemmas for finite weighted PMFs.
- `papers/IM05MarriageHonestyStability/MainTheorems.lean`: corrected generic
  tail-count Lemma 4.4 and Lemma 4.1 bridges, plus the generic two-draw
  weighted-without-replacement omission NC base.
- `papers/IM05MarriageHonestyStability/README.md`: named-result table and next
  target updated to use the corrected tail bridge.
- `papers/IM05MarriageHonestyStability/ProofStrategy.md`: active strategy
  updated to route Theorem 3.1 through the corrected tail-count branch.
