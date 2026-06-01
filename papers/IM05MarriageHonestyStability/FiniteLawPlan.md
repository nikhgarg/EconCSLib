# IM05 Lemma 4.4 Finite-Law Plan

Current target: prove the finite laws that identify the uniform integer-multiset
permutation events with the recursive raw-count fresh-list probabilities.

Verified induction primitives:

- `im05_decrementCount` removes one copy of a target name.
- `im05_sum_decrementCount_of_pos` and
  `im05_sum_decrementCount_add_one_of_pos` control the total length after a
  positive decrement.
- `im05_nameCountInWord_succ` splits a nonempty finite word into head plus tail.
- `im05_nameCountInWord_wordTail_eq_decrement` proves that if a word with count
  vector `count` starts with `target`, its tail has count vector
  `im05_decrementCount count target`.
- `im05_integerMultisetPermutationTailSampleOfHead` and
  `im05_integerMultisetPermutationConsSample` implement the two sample-space
  maps between the first-symbol fiber and the decremented sample space.
- `im05_integerMultisetPermutationTailSampleOfHead_consSample` proves the easy
  inverse direction.
- `im05_integerMultisetPermutationConsSample_tailSampleOfHead` proves the hard
  inverse direction by slot extensionality.
- `im05_integerMultisetPermutationHeadFiberEquiv` and
  `im05_integerMultisetPermutationFirstSigmaEquiv` package the head/tail
  decomposition as equivalences.
- `im05_integerMultisetPermutationReindexEquiv` proves slot-reindexing
  invariance for count-vector samples.
- `im05_integerMultisetPermutation_first_event_card_mul_total` double-counts
  target occurrences over all samples.
- `im05_integerMultisetPermutation_first_prob_eq_count_ratio` proves the exact
  first-symbol law `Pr[first = target] = count target / sum count`.
- `im05_algorithm42FreshList_countWeight_first_draw_prob_eq_count_ratio` and
  `im05_integerMultisetPermutation_first_prob_eq_countWeight_freshList_first_prob`
  close the base finite-law bridge between uniform count-vector words and the
  raw-count Algorithm 4.2 sampler.
- `im05_firstAppearanceList` is now the direct first-occurrence primitive
  `List.eraseDups`, with local no-duplicate, head, prefix-set, and
  `namesBeforeFirst` cardinal lemmas.
- `im05_integerMultisetPermutationFirstAppearanceFreshList_prefix_omits_iff_namesBeforeFirst_card`
  identifies the paper event `k ≤ namesBeforeFirst.card` with prefix omission
  in the first-appearance fresh list of a count-vector word.
- `im05_integerMultisetPermutationFirstAppearanceFreshList_first_prob_eq_countWeight_freshList_first_prob`
  upgrades the first-symbol bridge to the first-distinct-name process at slot
  zero.
- `im05_integerMultisetPermutation_base_finite_law_one` closes the exact
  marginal finite law for `k = 1`.
- `im05_namesBeforeFirst_erase_eq_namesBeforeFirst_filter_ne` and
  `im05_integerMultisetPermutation_namesBeforeFirst_erase_eq_allowedList`
  formalize the deletion identity: erasing `j` from names before first `i`
  equals filtering `j` out of the word before computing names before first `i`.
- `EconCSLib.pmfProb_uniformPMF_comp_eq_of_constant_fiber_card` is now a
  general library lemma: a finite map with constant positive fiber cardinality
  pushes the uniform law forward to the uniform law.
- `im05_integerMultisetPermutationAllowedSample_uniform_event_eq_of_constant_fiber`
  applies that library lemma to the IM05 allowed-sample projection, reducing the
  remaining projection step to a single constant-fiber cardinality theorem.
- `EconCSLib.finite_constant_fiber_card_comp` and
  `EconCSLib.finite_constant_fiber_card_equiv_comp` are now available for
  composing constant-fiber deletion maps and for post-composing with count-vector
  cast equivalences.
- `im05_countOutside_empty`, `im05_countOutside_countOutside_union`,
  `im05_countOutside_countOutside_singleton`,
  `im05_integerMultisetPermutationList_allowedSample`, and
  `im05_integerMultisetPermutationAllowedList_allowedSample` prove the
  deterministic count/list side of iterated forbidden-set deletion.
- `im05_integerMultisetPermutationAllowedSample_empty`,
  `im05_integerMultisetPermutationAllowedSample_empty_fiber_card`,
  `im05_integerMultisetPermutationAllowedSample_allowedSample`,
  `im05_integerMultisetPermutationAllowedSample_union_singleton_fiber_card_of_constant_fiber`,
  and `im05_integerMultisetPermutationAllowedSample_fiber_card_exists`
  package the full arbitrary-forbidden-set deletion fiber theorem by induction
  from the empty map and singleton deletion.
- `im05_integerMultisetPermutationAllowedSample_uniform_event_eq` is now the
  certificate-free uniform projection law for deleting any forbidden set.
- `im05_integerMultisetPermutationAllowedSample_first_prob_eq_count_ratio` and
  `im05_integerMultisetPermutationAllowedSample_first_prob_eq_countWeight_excluding`
  prove the first non-forbidden symbol law in ratio and Algorithm 4.2 atom
  forms.
- `im05_countWeight_freshList_conditional_first_eq_of_first_ne` proves the
  one-draw raw-count conditional atom formula: conditioning on not drawing
  `j` renormalizes the first draw by the available count outside `{j}`.
- `im05_countWeight_freshList_conditional_first_ne_eq_countOutside_first_ne_prob`
  converts that atom formula by complements into the residual count-vector
  first-symbol law.
- `im05_integerMultisetPermutation_conditional_finite_law_one_of_allowedSample_constant_fiber`
  closes the exact `k = 1` conditional finite law, with only the singleton
  allowed-sample constant-fiber cardinality still exposed as a combinatorial
  certificate.
- `im05_integerMultisetPermutationAllowedSampleSingletonFiberEquiv`,
  `im05_integerMultisetPermutationAllowedSample_singleton_fiber_card`, and
  `im05_integerMultisetPermutationAllowedSample_singleton_fiber_card_pos`
  discharge that certificate by reconstructing every preimage from the set of
  `excluded` slots and the residual word.
- `im05_integerMultisetPermutation_conditional_finite_law_one` is now the
  assumption-free exact `k = 1` conditional finite law.
- `im05_integerMultisetPermutation_base_finite_law_zero` and
  `im05_integerMultisetPermutation_conditional_finite_law_zero` close the
  trivial `k = 0` marginal and conditional finite laws.
- `im05_integerMultisetPermutationFirstAppearanceFreshList_prefix_two_omits_prob_eq_countWeight_freshList_prefix_two_omits_prob`
  and `im05_integerMultisetPermutation_base_finite_law_two` close the exact
  marginal finite law for `k = 2`.
- `im05_integerMultisetPermutation_erased_namesBeforeFirst_iff_allowedList_firstAppearance_not_mem_take`
  and
  `im05_integerMultisetPermutation_erased_namesBeforeFirst_prob_eq_countOutside_firstAppearance_not_mem_take`
  isolate the deterministic/projection half of singleton deletion for arbitrary
  `k`.
- `im05_integerMultisetPermutation_erased_namesBeforeFirst_prob_eq_countOutside_namesBeforeFirst`
  restates the same projection as an ordinary `namesBeforeFirst` event in the
  residual count-vector word.
- `im05_integerMultisetPermutation_countOutside_base_finite_law_one` closes
  the one-draw marginal finite law after an arbitrary initial forbidden set,
  giving the base case for an arbitrary-forbidden-set induction.
- `im05_two_le_namesBeforeFirst_card_iff_filter_ne_head_one_le` gives the
  deterministic `k = 2 -> k = 1` recursion after exposing a non-target head.
- `paper_im05_lemma4_4_freshList_conditional_comparison_from_integerMultiset_erased_upper_bound`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_erased_upper_bounds_and_scaled_count_limits`,
  and the `..._two` specialization expose the corrected finite-scale route:
  prove a conditional upper bound to the erased multiset event, then reuse
  deterministic inclusion and the marginal finite law.
- `paper_im05_lemma4_4_freshList_conditional_comparison_from_integerMultiset_finite_law_one`
  combines the two `k = 1` finite laws with the uniform multiset
  deletion/inclusion inequality to prove the raw-count one-man comparison for
  `k = 1`.
- `paper_im05_lemma4_4_freshList_conditional_comparison_from_integerMultiset_finite_law_zero`
  exposes the corresponding `k = 0` comparison base case.
- `im05_algorithm42FreshList_countWeight_two_hit_negative_correlation` proves
  direct two-draw negative correlation for the hit events by combining the exact
  two-slot atom formula, the one-target hit factor formula, finite sum splits
  outside `{i,j}`, and the scalar Plackett--Luce inequality
  `im05_two_draw_hit_negative_correlation_core_prob_shape`.
- `paper_im05_lemma4_4_freshList_pairwise_negative_correlation_countWeight_two`
  complements the hit-event inequality to the actual two-draw omission events.
- `paper_im05_lemma4_4_freshList_conditional_comparison_countWeight_two`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_scaled_count_negative_correlation_limits_two`,
  and
  `paper_im05_lemma4_4_variance_le_expectation_from_freshList_scaled_count_negative_correlation_limits_two`
  close the raw-count conditional comparison, the scaled-count limiting
  comparison, and the independent-men variance endpoint for `k = 2`.
- `finiteWithoutReplacementPMF_event_prob_succ_eq_sum_head`,
  `finiteWithoutReplacementPMF_omit_atom_succ_prob_eq_sum_head`, and
  `finiteWithoutReplacementPMF_omit_pair_succ_prob_eq_sum_head` give reusable
  first-step recurrences for arbitrary without-replacement events and omission
  events.
- `im05_plackettLuce_k3_omission_negative_correlation_counterexample_scalar`
  and `im05_plackettLuce_k3_conditional_comparison_counterexample_scalar`
  record an exact rational `k = 3` counterexample to the arbitrary-`k`
  negative-correlation/conditional-comparison claim for the Plackett--Luce
  fresh-list sampler.

Correction to the source route:

- The paper's finite-multiset paragraph states an equality between
  `Pr[F_i | F_j]` and the process obtained by deleting all copies of `j`.
  That equality is not true for nonuniform weights once `k >= 2`; a small
  Plackett-Luce calculation with weights `i=1, j=2, a=3, b=4` gives
  `Pr[F_i | F_j] = 0.66477...` but the deleted-`j` process gives `0.675`.
- The further upper-bound repair through deletion is also false.  With weights
  `i=2, j=1, a=1, b=1`, `Pr[F_i | F_j] = 0.17647...`, while the deleted-`j`
  process gives `0.16666...`.  The formal target must therefore be the
  negative-correlation inequality itself, not a deletion equality or deletion
  upper bound.

Next Lean steps:

1. Do not pursue the arbitrary-`k` one-man negative-correlation theorem as
   stated; it is false at `k = 3` for weights `[30, 1, 1, 1, 30, 1]`.
2. Decide on a corrected Lemma 4.4 route: a restricted special case, a weaker
   variance bound that survives the counterexample, or an explicit validation
   issue for the published proof.
3. In parallel, continue independent source branches: Algorithm 4.1/Theorem
   4.1 now has a paper-facing output certificate, abstract strict-preference
   ordered-list existence, shared arbitrary-start/divorce trace scaffolding,
   target-exception invariant preservation, final resumed-run wrappers, and the
   concrete held-men list's nodup/order proof. The remaining Algorithm 4.1
   obligation is the membership equality between held men and stable husbands.
   Lemma 4.2 now has expectation/reciprocal wrappers and is wired into a
   sampled-stable-matching Lemma 4.1 bridge; the concrete Algorithm 4.2 market
   sample still needs to feed those wrappers while Lemma 4.4 is under source
   correction.

Proof strategy for the recursive lift:

- The deterministic equivalence between `k ≤ namesBeforeFirst i` and omission
  of `i` from the first `k` first-appearance names is now proved.
- The deterministic deletion identity for the conditional event is now proved.
- Prove the next-new-name law by filtering away an already realized prefix:
  conditional on a fresh prefix `S`, the first symbol of the unfiltered
  residual word outside `S` has probability `count target / available(S)`.
  The base case is already verified by the first-symbol law; the remaining
  technical bridge is the constant-fiber/filtering argument that uniform
  count-vector words project to the uniform residual count-vector law.
- Once exact prefix-list atom probabilities match Algorithm 4.2 atom weights,
  sum over prefix atoms to get the marginal and conditional finite laws.

Strategic note: the conditional law is not the same as simply forbidding `j`
from the start of the recursive sampler.  The named finite multiset route must
therefore be corrected to a negative-dependence or upper-bound statement rather
than a deletion equality.
