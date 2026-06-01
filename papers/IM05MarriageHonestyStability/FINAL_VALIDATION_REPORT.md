# Final Validation Report: Immorlica--Mahdian 2005

## 1. Source and Scope

- Paper: *Marriage, Honesty, and Stability*
- Authors: Nicole Immorlica and Mohammad Mahdian
- Source version checked: MIT-LCS-TR-913 technical report, PDF created
  April 11, 2005; also published in SODA 2005.
- Lean folder: `papers/IM05MarriageHonestyStability`
- Main theorem file: `papers/IM05MarriageHonestyStability/MainTheorems.lean`
- Status table: `papers/IM05MarriageHonestyStability/README.md`
- Live proof plan: `papers/IM05MarriageHonestyStability/ProofStrategy.md`
- Handoff note: `papers/IM05MarriageHonestyStability/NEXT_AGENT_HANDOFF.md`
- Source issue report:
  `papers/IM05MarriageHonestyStability/LEMMA4_4_COUNTEREXAMPLE_REPORT.md`

## 2. Paper Definitions Checked

- Stable matching, stable husbands/wives, and multiple-stable-partner counts:
  formalized in `MainTheorems.lean` and backed by reusable matching
  infrastructure in `EconCSLib/Markets/Matching`.
- Men- and women-proposing deferred acceptance:
  represented through reusable DA APIs, with IM05 wrappers for Theorems A-D.
- Random length-`k` lists from `D^k`:
  represented by the recursive fresh-list / weighted-without-replacement
  sampler.  This matches the source's repeated independent draws from `D` with
  repetitions removed.
- Algorithm 4.1 resumed proposal process:
  represented by target-divorce and arbitrary-start DA state wrappers.
- Algorithm 4.2 fresh-list deferred-decision process:
  represented by prefix-set and conditional atom formulas for the concrete
  fresh-list PMF.
- Occupancy variables for Section 6:
  represented by reusable finite occupancy APIs in
  `EconCSLib/Foundations/Probability/Occupancy.lean`.

## 3. Named-Result Validation

The README contains the full declaration-level inventory.  `DependencyDAG.tex`
was refreshed on May 16, 2026 against that initial named-result inventory and
uses the controlled README/DAG status vocabulary.  Paper-level status:

Pause verdict: as of the May 16, 2026 handoff, this is not a completed
verification and not a cleanup-only task.  The development has closed a large
amount of matching, probability, and algebraic infrastructure, but the main
paper results still depend on three proof campaigns: the Algorithm 4.1
pair-witness completion certificate, the repaired Lemma 4.4 tail-variance input
and stable-market wiring for Theorem 3.1, and the concrete Section 6
experiment construction for Theorem 3.2.

- Theorems A-D: conditionally complete on the documented strict/equal-size
  complete-domain wrappers; optional-domain variants remain caveated.
- Conjecture 1 / Theorem 3.1: incomplete with validation issue.  The algebraic
  summation and asymptotic endpoint are formalized, but the probabilistic proof
  path depends on a corrected replacement for Lemma 4.4.
- Theorem 3.2: conditional.  The algebraic endpoint from Lemmas 6.1-6.3 is
  formalized, but the full experiment construction and one Experiment 3
  probability argument remain open.
- Corollaries 3.1-3.3: partially formalized.  The finite symmetry and
  asymptotic probability bridges are present; the full mechanism/incentive
  wrappers remain open.
- Algorithm 4.1 / Theorem 4.1: conditional.  The output certificate surface,
  corrected target-divorcing trace, accepted-men list, nodup/order facts,
  forward inclusion, and worst-stable-husband base case are present.  The older
  non-divorcing `DAState` held-men trace is scaffold only; the source-faithful
  endpoint now targets `im05_algorithm41SourceDivorceTargetAcceptedMen`.  The
  strongest current one-stop wrapper is
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`,
  and the exact remaining certificate is
  `im05_Algorithm41SourcePairWitnessCompletionCertificate`.  The
  first target-threshold primitives are now present:
  `im05_algorithm41TargetAccepts`,
  `im05_algorithm41TargetStandardAfterAccept`, and
  `im05_algorithm41TargetStandard_value_mono_of_accepts`.  The proposal-history
  side of the source rule is also formalized through
  `im05_algorithm41HasProposedTo`, `im05_algorithm41HistoryAccepts`,
  `im05_algorithm41BestProposedSoFar`,
  `im05_algorithm41BestProposedSoFar_after_history_accept`, and
  `im05_algorithm41HistoryAccepts_of_bestProposedSoFar_of_targetAccepts`.
  The bridge
  `im05_algorithm41HistoryAccepts_of_womanRejectionInvariantExcept_current_lt`
  formalizes the paper's claim that, away from the target woman, comparing
  against the current match agrees with comparing against the best proposer so
  far under the usual rejection invariant.  `im05_algorithm41SourceStepAccepts`
  packages the chosen-proposal source acceptance seam, with wrappers for the
  target-standard and non-target current-match cases.  `im05_algorithm41SourceStep`
  is the corresponding one-step transition, with basic lemmas proving that an
  active source-shaped step removes and records the selected proposal.  The
  source trace now also has named finite-run/final-state/held-men wrappers,
  full source-step preservation of the target-exception invariant package on
  all-acceptable domains, source-final stable-except-target semantics, an
  initial-divorce best-so-far theorem, preservation that any current target
  holder is best-so-far, preservation of a nonnegative target best-so-far
  proposer from the initial DA match, target held-value monotonicity along the
  source run, a proof that any source final target holder is a stable husband,
  source-held-men nodup/membership facts, and a source-held-men worst-to-best
  output certificate conditional on the remaining source-held-men/stable-husbands
  membership equality.  Rechecking Step 4(b) exposed one more source-model
  correction: when `w = g` accepts, the paper immediately returns to Step 2,
  outputs that man, and divorces him.  The corrected surface now includes
  `im05_algorithm41SourceStepTargetAccepted`,
  `im05_algorithm41SourceStepDivorceTarget`,
  `im05_algorithm41SourceDivorceTargetStateAfterSteps`,
  `im05_algorithm41SourceDivorceTargetFinalState`, and
  `im05_algorithm41SourceDivorceTargetAcceptedMen`, with a finite termination
  theorem for the target-divorcing run.  The corrected trace now also has
  target-divorcing invariant preservation, target-unmatched prefix/final facts,
  proposal-history shrinkage, no-repeat target-acceptance events, initial-husband
  non-reappearance, accepted-men nodup/order proofs, and corrected output
  certificate wrappers conditional on accepted-men/stable-husbands membership.
  The forward inclusion is now closed for all-acceptable domains:
  `im05_algorithm41SourceDivorceTargetAcceptedMen_forward_of_allPairsAcceptable`
  proves every corrected accepted-men output is a stable husband, and the
  witness-form variants return an explicit stable matching with
  `m_match m = some g`.  The base case
  `paper_im05_theorem4_1_base_case_worst_stable_husband` proves the first DA
  husband is `g`'s worst stable husband on the strict equal-size all-acceptable
  domain.  The final wrapper
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_card_lower`
  reduces the remaining bridge to proving enough accepted-men outputs, while
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_backward`
  remains the pointwise backward-inclusion route.  The local rejection bridge
  `im05_algorithm41SourceStep_target_reject_not_mem_stableHusbands_of_rejected_pair_impossible_except_target`
  is closed; it needs the target-exception rejected-pair invariant because
  accepted target pairs are intentionally removed and can still be stable.
  The current-match-order assumption in that bridge is now automatic along the
  corrected trace:
  `im05_deferredAcceptanceState_currentMatchOrder_of_allPairsAcceptable`,
  `im05_algorithm41DivorcedState_currentMatchOrder_of_allPairsAcceptable`, and
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_currentMatchOrder_of_allPairsAcceptable`
  are closed.  The source accept test is also proved equivalent to ordinary DA
  under full invariants and for non-target women under target-exception
  invariants.  The remaining backward-inclusion obligation is packaged by
  `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_trace_target_proposals`
  and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals`.
  Target-exception rejected-pair preservation is validated for target-only
  active prefixes by
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_target_chosen_prefix`;
  the general non-target-step case is now isolated by
  `im05_SourceStepNonTargetRejectedPairExclusions`,
  `im05_SourceStepNonTargetRejectedPairExclusions_of_full_rejectedPairImpossible`,
  `im05_algorithm41SourceStepDivorceTarget_preserves_rejectedPairImpossibleExceptWoman_of_stepNonTargetExclusions`,
  and
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_stepNonTargetExclusions_prefix`.
  The strongest current final wrapper,
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`,
  requires only those per-step exclusions plus stable-husband target-proposal
  coverage.  Those per-step exclusions are further reduced by
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_rejectedPairImpossibleExceptTarget_of_exception_partner_exclusions_prefix`
  to exception-partner side conditions: the prior/chosen proposer used in a
  non-target blocking argument must not be matched to `g` in the candidate
  stable matching.  The compact prefix predicate is
  `im05_SourceTraceExceptionPartnerExclusions`, and the corresponding final
  conditional wrapper is
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceExceptionPartnerExclusions`.
  This side condition is now further reduced to stable-husband-set exclusions:
  `im05_SourceStepNonTargetBlockersNotStableHusbands` gives the one-step local
  obligation, `im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers`
  lifts it to the trace predicate
  `im05_SourceTraceNonTargetBlockersNotStableHusbands`, and that trace predicate
  implies the compact exception-partner predicate via
  `im05_SourceTraceExceptionPartnerExclusions_of_nonTargetBlockersNotStableHusbands`,
  and the paper-facing wrapper
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_nonTargetBlockersNotStableHusbands`
  packages that implication.  The direct one-step paper-facing wrapper is
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.
  The target-proposal coverage side is also narrowed to the source algorithm:
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial` excludes
  the initial DA husband already output before the loop, and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`
  is the strongest current final wrapper.
  Coverage can now be derived from final proposal-set removal using
  `im05_algorithm41SourceDivorceTargetStateAfterSteps_removed_proposal_exists_chosen`
  and
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_removed_target_proposals`;
  the corresponding final wrapper is
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`.
  The start-available part of that condition is now closed on the strict
  equal-size all-acceptable domain by
  `im05_noninitial_stableHusband_mem_divorced_proposals`; the strongest current
  wrapper is
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`,
  which requires one-step blocker exclusions and final target-removal for
  non-initial stable husbands.
  Final target-removal is reduced further to a final-match preference premise
  by `im05_not_mem_proposals_of_terminated_prefers_target_to_current` and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands_of_card_eq`.
  These equal-size wrappers remove the explicit initial-husband witness from
  the intermediate paper-facing layers.
  Matching equal-size wrappers at the trace-coverage layer now do the same for
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial`.
  The blocker side also has
  `im05_mem_stableHusbands_iff_exists_stable_exception_match` and
  `im05_not_mem_stableHusbands_iff_forall_stable_not_exception_match`, an
  interface between stable-husband membership/non-membership and direct
  matching witness/exclusion forms for `g`.
  The trace/per-step blocker predicates are equivalent via
  `im05_SourceTraceNonTargetBlockersNotStableHusbands_iff_stepBlockers`.
  The local blocker package is reduced further to the stronger stable-matching
  exclusion interface
  `im05_SourceStepNonTargetStableMatchExclusions`.
  The same reduction is packaged at the trace level by
  `im05_SourceTraceNonTargetStableMatchExclusions`.
  The reduced condition now also feeds the rejected-pair preservation layer
  through
  `im05_SourceStepNonTargetRejectedPairExclusions_of_stableMatchExclusions`
  and the trace/step prefix rejected-pair-impossibility wrappers.
  A more direct non-target route is also available:
  `im05_SourceStepNonTargetBlockingPreferences` packages the exact blocking
  inequalities needed for rejected and displaced non-target pairs, with
  trace-level rejected-pair preservation, source-faithful except-initial
  wrappers, and a final-removal endpoint.  The sharper pair-level variant
  `im05_SourceStepNonTargetBlockingPairPreferences` weakens the accepted-step
  premise to only candidate stable matchings that keep the displaced pair, and
  now has full target-proposal, except-initial, and final-removal wrappers.
  The stronger stable-match exclusion route now also supplies this sharper
  pair-level route through
  `im05_SourceStepNonTargetBlockingPairPreferences_of_stableMatchExclusions`
  and
  `im05_SourceTraceNonTargetBlockingPairPreferences_of_stableMatchExclusions`;
  the broader direct blocking-preference predicate also coerces to pair-level
  through the corresponding `_of_blockingPreferences` lemmas.  The pair-level
  and broader blocking-preference final-removal endpoints now have direct
  projection corollaries for the inclusion, set-equality, length, and order
  components of Theorem 4.1.  The preferred reduced contract is bundled as
  `im05_Algorithm41SourcePairCompletionCertificate`, with a one-stop
  paper-facing output wrapper.  A weaker rejection-side route is also
  available through `im05_SourceStepNonTargetBlockingPairWitnessPreferences`:
  it asks for one prior blocking proposer rather than all better prior
  proposers, and has trace/final-removal paper wrappers.  Its compact
  certificate is `im05_Algorithm41SourcePairWitnessCompletionCertificate`.
  The target-only-prefix special case discharges stable-match exclusions
  vacuously and has a direct paper-facing output wrapper.
  The trace-coverage theorem now exposes direct stable-match-exclusion wrappers:
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceStableMatchExclusions`
  and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepStableMatchExclusions`.
  The current reduced endpoint is also packaged directly as
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalPref_of_card_eq`,
  using stable-match exclusions plus the matched-final-assignment preference
  premise.
  The compact final-target-blocking variant is packaged by
  `im05_Algorithm41SourceCompletionCertificate_of_stableMatchExclusions_finalTargetBlocks`
  and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_stableMatchExclusions_finalTargetBlocks_of_card_eq`.
  Final target-proposal removal now implies the compact final-target-blocking
  field through
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_final_target_removed`,
  yielding the combined stable-exclusion/final-removal endpoint; the reverse
  final-blocking-to-final-removal direction and iff are also formalized.
  Direct projection corollaries expose the same reduced assumptions when only
  backward inclusion, finset equality, length equality, or worst-to-best order
  is needed.
  The bundled remaining-obligation target is now
  `im05_Algorithm41SourceCompletionCertificate`, and
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate`
  derives the paper-facing output contract from it.
  The equal-size wrapper
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate_of_card_eq`
  removes the explicit initial-husband witness by deriving it internally from
  equal cardinality and all-acceptable preferences.
  The final-match field of that certificate now also has the compact
  target-blocking interface
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks`, with bridge theorem
  `im05_SourceFinalNoninitialStableHusbandTargetBlocks.finalPref`, matched-case
  constructors `im05_SourceFinalNoninitialStableHusbandTargetBlocks_of_finalPref`
  and `im05_SourceFinalNoninitialStableHusbandTargetBlocks_iff_finalPref`,
  direct trace-coverage bridge
  `im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial_of_finalTargetBlocks_of_card_eq`,
  constructors `im05_Algorithm41SourceCompletionCertificate_of_finalTargetBlocks`
  and `im05_Algorithm41SourceCompletionCertificate_of_finalPref`, and
  one-stop matched-final-preference wrapper
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalPref_of_card_eq`,
  plus
  paper-facing wrapper
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks`.
  The direct backward-inclusion corollary
  `im05_stableHusbands_subset_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`
  exposes the stable-husbands-subset-output part alone, and
  `im05_algorithm41SourceDivorceTargetAcceptedMen_toFinset_eq_stableHusbands_of_finalTargetBlocks_of_card_eq`
  and
  `im05_algorithm41SourceDivorceTargetAcceptedMen_length_eq_stableHusbands_card_of_finalTargetBlocks_of_card_eq`
  expose the direct finset and length equalities; the companion
  `im05_algorithm41SourceDivorceTargetAcceptedMen_worstToBest_of_finalTargetBlocks_of_card_eq`
  exposes the direct order projection.
  Under all-acceptable preferences, the `valM` unmatched case is automatic.
  The current preferred paper-facing endpoint is the equal-size wrapper
  `paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_finalTargetBlocks_of_card_eq`.
  The non-divorcing source-held-men trace is therefore a scaffold; the final
  Theorem 4.1 proof should target the accepted-men event list.
- Algorithm 4.2: partially formalized.  The concrete fresh-list PMF, prefix
  laws, and Lemma 4.3 ranked-tail product route are substantially developed.
  The repaired route now has direct rank-index Lemma 4.1 endpoints for
  negative correlation, constant-factor variance, conditional comparison,
  multiset limits, and finite-weight limits over a selected `Fin N` popularity
  tail.  The source final summation range is packaged as
  `im05_sourceRankTailBlock`, with side-condition and lower-rank count bridges,
  plus source-range Lemma 4.1 wrappers matching the paper's `X_mu(g) >= Y_g`
  count shape for direct conditional-comparison, multiset-limit, and
  finite-weight-limit inputs.  A finite source-tail pairwise negative
  correlation bridge now also feeds the conditional-comparison input expected
  by the finite-weight route, and the corresponding source-range
  finite-weight Lemma 4.1 wrapper composes directly from that pairwise negative
  correlation input.
- Lemma 4.1: conditionally complete.  The Chebyshev/variance bridge is closed
  once a valid variance input is supplied.
- Lemma 4.2: formalized with caveat.  The deterministic and expectation
  wrappers are present; full paper wiring needs the concrete Algorithm 4.2
  sample and matching choice.
- Lemma 4.3: partially formalized.  The ranked-tail product lower-bound route
  is substantially formalized.
- Lemma 4.4: source statement false as printed for arbitrary nonuniform `D^k`.
  See Section 6 below.
- Lemma 6.1: conditional on Lemma 6.2.
- Lemma 6.2: conditional.  The five-experiment expectation chain and
  perturbation algebra are formalized, but concrete experiment wiring and the
  Experiment 3 per-pair probability proof remain open.
- Lemma 6.3: complete.
- Appendix Lemmas A.1-A.2: not started.

## 4. Additional Assumptions and Modeling Notes

- Lean uses finite types and decidable equality throughout.
- Several matching preliminaries are closed on strict, all-acceptable,
  equal-cardinality marriage domains.  The source often speaks informally
  through standard DA facts; the current wrappers expose the needed domain
  assumptions explicitly.
- The arbitrary nonuniform `D^k` list model is represented as
  Plackett--Luce top-`k` sampling by repeated draws with repetitions removed.
  This is not an extra assumption; it is the source model.

## 5. Proof-Strategy Deviations

- The DA preliminaries are reused from the Roth/Gale-Shapley infrastructure
  rather than reproved from scratch.
- Section 6's occupancy proof uses reusable finite occupancy lemmas rather
  than following every inclusion-exclusion manipulation from the paper.
- Theorem 3.1 cannot continue through Lemma 4.4 as printed.  The Lean file now
  has a corrected tail-count bridge,
  `paper_im05_lemma4_4_tail_variance_le_expectation_of_pairwise_negative_correlation`,
  and the corresponding Lemma 4.1 bridge,
  `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3`.  These
  replace the full `Y_g` variance lemma with a concentration statement over an
  explicit rank-tail block aligned with Lemma 4.3's lower-bound sum.  The
  concrete Algorithm 4.2 route now has tail-only wrappers through the Lemma 4.3
  lower bound, full-support one-man conditional comparison, multiset limits, and
  weight limits, plus a source-range finite-weight endpoint that assumes only
  finite-scale pairwise negative correlation on the source tail.  The repaired
  branch no longer requires the false all-pairs comparison.  There is also a
  constant-factor fallback
  `paper_im05_lemma4_1_from_tail_variance_factor_and_lemma4_3`, which is enough
  for the asymptotic endpoint if one can prove
  `Var(Y_tail) <= C * E[Y_tail]` for fixed `C`.  The remaining mathematical
  obligation is the stochastic tail negative-correlation input or a direct
  constant-factor tail-variance input for the concrete fresh-list law.  The
  finite induction route now has compiled one-head and two-head omission
  recurrences, compact first-step sums, pairwise-NC base cases, a generic
  `im05_tailDepth` predicate, positive-residual and two-step induction
  reductions, a closed generic two-draw weighted-without-replacement omission
  NC theorem, and source-tail wrappers.  The strongest current reduction is
  `im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_firstStep_family`:
  it reduces the source-tail input to compact first-step averaging only for
  residual lengths at least two.  The boundary cases where one target is
  already forbidden are now closed by
  `im05_omissionPairNegativeCorrelation_of_left_mem_forbidden` and
  `im05_omissionPairNegativeCorrelation_of_right_mem_forbidden`, yielding
  `im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_firstStep_family`;
  this sharper route only asks for first-step averaging when both targets are
  still available.  At the compact-sum level, the boundary algebra is also
  closed by `im05_firstStepOmitPairProductSum_comm`,
  `im05_firstStepOmitMarginalSum_eq_one_of_mem_forbidden`,
  `im05_firstStepOmitPairProductSum_eq_marginal_of_left_mem_forbidden`,
  `im05_firstStepOmitPairProductSum_eq_marginal_of_right_mem_forbidden`, and
  `im05_firstStepOmitPairProductSum_le_mul_of_available_firstStep`.  The named
  sums now also have probability bounds
  `im05_firstStepOmitMarginalSum_le_one`,
  `im05_firstStepOmitPairProductSum_le_marginal_left`, and
  `im05_firstStepOmitPairProductSum_le_marginal_right`.  The weighted
  opposite-spread algebra
  `im05_weighted_opposite_spread_identity`,
  `im05_weighted_product_sum_le_product_sums_of_opposite_spread_nonneg`, and
  `im05_weighted_product_sum_le_product_sums_of_pairwise_opposite` is compiled,
  `im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread_sum_nonneg`
  specializes the exact summed-spread condition to the compact first-step sums,
  and `im05_firstStepOmitPairProductSum_le_mul_of_head_opposite_spread`
  provides the stronger pointwise shortcut.  The named compact API
  `im05_firstStepHeadWeight`, `im05_firstStepResidualOmitProb`,
  `im05_firstStepResidualSpreadSum`,
  `im05_firstStepResidualSpreadSum_comm`,
  `im05_firstStepResidualSpreadSum_nonneg_of_pairwise_opposite`,
  `im05_firstStepResidualSpreadSum_eq_two_mul_gap`,
  `im05_firstStepResidualSpreadSum_nonneg_iff`,
  `im05_firstStepResidualSpreadSum_nonneg_zero_of_ne`,
  `im05_firstStepHeadWeight_nonneg`, `im05_firstStepHeadWeight_le_one`,
  `im05_firstStepResidualOmitProb_eq_zero_of_head_eq`,
  `im05_firstStepResidualOmitProb_eq_prob_of_head_ne`,
  `im05_firstStepResidualOmitProb_nonneg`,
  `im05_firstStepResidualOmitProb_le_one`,
  `im05_firstStepOmitMarginalSum_eq_headWeight_residual`,
  `im05_firstStepOmitPairProductSum_eq_headWeight_residual_product`, and
  `im05_firstStepOmitPairProductSum_le_mul_of_residual_spread_sum_nonneg`
  is the preferred surface for continuing this proof.  The pointwise shortcut
  is also named as
  `im05_firstStepOmitPairProductSum_le_mul_of_residual_pairwise_opposite`.
  The shorter named-sum theorem is
  `im05_firstStepOmitPairProductSum_le_mul_of_residualSpreadSum_nonneg`.
  The exact residual-spread condition now feeds the available-state induction
  through
  `im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_available_residual_spread_family`
  and its source rank-block specialization
  `im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_available_residual_spread_family`.
  The paper-facing endpoints are
  `paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_residual_spread_averaging`
  and
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residual_spread_and_lemma4_4`.
  The shortest Lemma 4.1 endpoint is
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_residualSpreadSum_and_lemma4_4`.
  The finite-weight approximation analogue is
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_residualSpreadSum_and_lemma4_4`.
  The paper-facing wrapper
  `paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_firstStep_averaging`
  now exposes that reduction directly for the Algorithm 4.2 source-tail pairwise
  NC statement, and
  `paper_im05_sourceRankTailBlock_freshList_pairwise_negative_correlation_from_available_firstStep_averaging`
  exposes the available-state version.  The generic surface wrapper
  `im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_firstStep_averaging`
  exposes the same reduction for arbitrary concrete targets with supplied
  tail-depth facts; the available-state generic wrapper is
  `im05_algorithm42FreshList_pairwise_negative_correlation_from_tailDepth_available_firstStep_averaging`.
  The wrapper
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_firstStep_averaging_and_lemma4_4`
  composes the same first-step averaging input directly to the corrected
  source-range Lemma 4.1 reciprocal bound for the full-support fresh-list law,
  and
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_available_firstStep_averaging_and_lemma4_4`
  does the same from the available-state first-step input.
  The finite-approximation wrapper
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_firstStep_averaging_and_lemma4_4`
  additionally composes finite-scale tail-depth facts plus first-step averaging
  through the weight-limit route; the available-state analogue
  `paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_tailDepth_available_firstStep_averaging_and_lemma4_4`
  does the same when finite-scale first-step averaging is proved only for
  targets still outside the forbidden set.
  This is a genuine proof-strategy deviation.
- The current Algorithm 4.1 trace work is also a scaffold rather than a
  source-faithful trace.  The source's Step 4(a) says `g` compares a suitor to
  the best man who has proposed to her so far after divorce; a plain consistent
  `DAState` cannot store that remembered threshold once `g` is unmatched.
  Future Algorithm 4.1 work should use the proposal-history standard instead
  of proving the current resumed-DA trace as the paper algorithm.  The minimal
  target-standard predicate, update monotonicity lemma, source-history
  accept/best-so-far lemmas, non-target current-match/history bridge,
  chosen-proposal source acceptance predicate, source-shaped one-step
  transition, finite source-run wrappers, source target-value monotonicity,
  source invariant preservation, source-final stable-except-target semantics,
  a source-final-holder stable-husband bridge, source-held-men output
  certificate, and a corrected target-divorcing accepted-men trace have been
  added as the starting point for that corrected trace model.

## 6. Suspected Paper Errors or Inconsistencies

Lemma 4.4 is false as stated for the paper's arbitrary nonuniform `D^k` model.

The proof claims that conditioning on a woman being absent from the first `k`
distinct names is equivalent to deleting all copies of that woman from the
multiset/permutation process.  That equivalence is false for nonuniform
weights.

There is a standalone finite counterexample in
`LEMMA4_4_COUNTEREXAMPLE_REPORT.md`.  It uses five men, five women, `k = 3`,
and weights `[50, 50, 1, 1, 1]`.  The report shows directly that
`Var(Y_g) > E[Y_g]` for `g = 2`, contradicting the printed Lemma 4.4.

This does not by itself disprove the main asymptotic theorem.  The main proof
uses concentration in a high-rank regime after Lemma 4.3, and a different
tail-variance argument may still be enough.  It does mean the published proof
route is incomplete for arbitrary nonuniform `D`.

## 7. Verification Status

The last Lean target build before this report was:

```text
lake build IM05MarriageHonestyStability
```

It completed successfully after adding the corrected tail-count Lemma 4.4 and
Lemma 4.1 bridges, the concrete Algorithm 4.2 tail wrappers, the
constant-factor variance fallback, the rank-index Lemma 4.1 endpoints, and the
rank-block/source-range side-condition and Lemma 4.1 wrappers.

The same target was rebuilt successfully on May 15, 2026 after adding the
source-range pairwise-NC-to-finite-weight endpoint and the finite induction
scaffolding for the repaired tail variance route.  It was rebuilt again on
May 15, 2026 after adding the compact first-step sums, the `im05_tailDepth`
induction theorem, and the source-tail first-step-family reduction.

It was target-checked again on May 15, 2026 after adding the positive-residual
and two-step source-tail reductions, the generic two-draw base, and the
Algorithm 4.1 stable-except-target/no-target-block bridge:
`lake env lean papers/IM05MarriageHonestyStability/MainTheorems.lean` completed
successfully with only pre-existing warnings.

The full paper target was then rebuilt successfully on May 15, 2026:
`lake build IM05MarriageHonestyStability`.

It was rebuilt successfully again on May 15, 2026 after adding the paper-facing
arbitrary-real-weight `k = 2` fresh-list negative-correlation wrapper, the
Algorithm 4.1 threshold-model caveat comment, and the paper-facing source-tail
first-step-averaging reduction wrapper.  The target-standard acceptance
primitives for a future source-faithful Algorithm 4.1 trace were then included
in another successful `lake build IM05MarriageHonestyStability` run.

The full paper target was rebuilt again on May 15, 2026 after adding the
Algorithm 4.1 proposal-history accept/best-so-far layer and the non-target
current-match/history compatibility bridge, then again after adding the
chosen-proposal source acceptance seam and source-shaped one-step transition:
`lake build IM05MarriageHonestyStability` completed successfully.

The full paper target was rebuilt again on May 15, 2026 after adding the
source-step/ordinary-DA equivalence lemmas, automatic current-match-order
bridges for the corrected Algorithm 4.1 trace, target-only and per-step-exclusion
rejected-pair prefix preservation, and the trace-coverage wrappers
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals`
and
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetExclusions`,
then again after reducing the per-step predicate to
`im05_SourceTraceExceptionPartnerExclusions` and adding
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_traceExceptionPartnerExclusions`,
and then after adding the stable-husband-set reduction
`im05_SourceTraceNonTargetBlockersNotStableHusbands` and the paper-facing
wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_nonTargetBlockersNotStableHusbands`,
and then after adding the step-local blocker predicate
`im05_SourceStepNonTargetBlockersNotStableHusbands`, its trace lift
`im05_SourceTraceNonTargetBlockersNotStableHusbands_of_stepBlockers`, and the
paper-facing one-step wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_of_stepNonTargetBlockersNotStableHusbands`,
and then after adding the source-faithful except-initial coverage predicate
`im05_SourceTraceStableHusbandTargetProposalCoverageExceptInitial` plus the
final wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_trace_target_proposals_except_initial_of_stepNonTargetBlockersNotStableHusbands`,
and then after adding proposal-removal trace extraction and the removed-target
final wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_removed_target_proposals_of_stepNonTargetBlockersNotStableHusbands`,
and then after closing the strict-domain start-available side via
`im05_noninitial_stableHusband_mem_divorced_proposals` and adding
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_target_removed_of_stepNonTargetBlockersNotStableHusbands`,
and then after adding the terminal-state final-match preference reduction
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_final_prefers_target_of_stepNonTargetBlockersNotStableHusbands`,
then after adding equal-size variants of the final-removal and final-preference
Algorithm 4.1 wrappers,
and then after adding the bundled remaining-obligation certificate
`im05_Algorithm41SourceCompletionCertificate` and wrapper
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_sourceCompletionCertificate`,
then after adding the final-target-blocking Algorithm 4.1 bridge and equal-size
paper-facing wrappers, and then after adding the
source-range Lemma 4.1 first-step-averaging composition wrapper, and then after
adding the generic Algorithm 4.2 tail-depth/first-step NC wrapper and the
finite-approximation weight-limit first-step wrapper, and then after adding
the available-target first-step induction and source-range Lemma 4.1 wrapper,
and then after adding the available-target finite-weight Lemma 4.1 wrapper,
and then after adding the compact first-step boundary algebra and probability
bounds, and then after adding the weighted opposite-spread first-step algebra,
and then after adding the named compact first-step residual-spread API:
`lake build IM05MarriageHonestyStability` completed successfully.

## 8. Recommended Pickup Point

Start with `NEXT_AGENT_HANDOFF.md`.  The recommended proof branch is the
corrected Lemma 4.1 route:

1. Instantiate the tail set in
   `paper_im05_lemma4_1_from_tail_negative_correlation_and_lemma4_3` with the
   rank range used by the Lemma 4.3 lower-bound sum.
2. Reuse the existing Lemma 4.3 lower-bound machinery to discharge the tail
   expectation hypothesis.
3. Establish a valid negative-correlation bound for that tail variable under
   the concrete fresh-list law, or prove a direct constant-factor bound
   `Var(Y_tail) <= C * E[Y_tail]`; if both fail, find a new counterexample.
4. Feed that stochastic input into the corrected exact tail bridge or the
   constant-factor bridge.

If that branch stalls, switch to Algorithm 4.1/Theorem 4.1.  The corrected
target-divorcing trace is now the source-facing endpoint, and the proposal
history/target-threshold primitives are already present.  The current reduced
target is `im05_Algorithm41SourcePairWitnessCompletionCertificate`, used by
`paper_im05_theorem4_1_from_algorithm41_sourceDivorceTargetAcceptedMen_of_pairWitnessCompletionCertificate_of_card_eq`.
That certificate packages the remaining non-target blocking-pair witness
preference obligation and final target-removal obligation for non-initial
stable husbands.
