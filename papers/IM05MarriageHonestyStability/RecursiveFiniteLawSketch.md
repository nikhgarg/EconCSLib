# Recursive Finite-Law Sketch

Goal: turn the closed singleton-deletion theorem into the recursive finite law
needed by Lemma 4.4 for arbitrary fresh prefixes.

The useful abstraction is not paper-specific:

1. If `f : A -> B` has every fiber of size `a`, and `g : B -> C` has every
   fiber of size `b`, then `g ∘ f` has every fiber of size `a * b`.
2. For count-vector samples, deleting `insert x S` should be the same map as
   deleting `S` first and then deleting `{x}` from the residual count vector:
   `countOutside (countOutside count S) {x} = countOutside count (insert x S)`
   and the corresponding `AllowedSample` maps agree up to that definitional
   count-vector equality.
3. The singleton fiber theorem applies to the second map in step 2, so an
   induction over the finite prefix set gives constant fibers for deletion of
   every realized prefix set.

Once that arbitrary-prefix projection law is available, the finite-law proof
can condition on a realized first-appearance prefix `S`: the residual word
outside `S` is uniform over the residual count vector, so the next new name has
probability `count target / available(S)`, matching the recursive
without-replacement sampler.

Immediate Lean sequence:

1. Add the generic constant-fiber composition lemma to
   `EconCSLib/Foundations/Probability/FiniteExpectation.lean`.
2. Prove the deterministic `countOutside` and `AllowedList`/`AllowedSample`
   composition lemmas locally in the IM05 file.
3. Package an arbitrary finite-set deletion constant-fiber theorem by induction
   on the forbidden set, using the singleton theorem at each insert step.

Progress:

- Step 1 is done as `EconCSLib.finite_constant_fiber_card_comp`, with the
  codomain-equivalence helper
  `EconCSLib.finite_constant_fiber_card_equiv_comp`.
- The count/list part of step 2 is done:
  `im05_countOutside_countOutside_union`,
  `im05_integerMultisetPermutationList_allowedSample`, and
  `im05_integerMultisetPermutationAllowedList_allowedSample`.
- The direct sample-level composition theorem exposed dependent cast friction:
  deleting `S` and then `{x}` lands in
  `countOutside (countOutside count S) {x}`, while deleting `insert x S` lands
  in an extensionally equal count vector.  The next implementation should use
  an explicit count-vector cast/equivalence API rather than dependent
  elimination on the function equality inside the main proof.
- That cast interface is now in place:
  `im05_integerMultisetPermutationList_countEquiv`,
  `im05_integerMultisetPermutationCountEquiv_apply_symm`, and
  `im05_integerMultisetPermutationCountEquiv_symm_apply`.
- Step 3 is done as
  `im05_integerMultisetPermutationAllowedSample_fiber_card_exists`, with the
  certificate-free projection theorem
  `im05_integerMultisetPermutationAllowedSample_uniform_event_eq`.
- The first residual draw law is done in both ratio form and Algorithm 4.2
  atom form:
  `im05_integerMultisetPermutationAllowedSample_first_prob_eq_count_ratio` and
  `im05_integerMultisetPermutationAllowedSample_first_prob_eq_countWeight_excluding`.
- The conditional-uniform projection lemma is now in the probability library as
  `EconCSLib.pmfConditionalProb_uniformPMF_comp_eq_of_constant_conditional_fiber_card`.
  The IM05 specialization
  `im05_integerMultisetPermutationAllowedSample_head_conditional_uniform_event_eq`
  proves that conditioning on a fixed first name and then deleting all copies of
  that name leaves a uniform residual word.
- The first recursive transition after a fixed head is done:
  `im05_integerMultisetPermutationAllowedSample_head_conditional_first_prob_eq_available_ratio`
  and
  `im05_integerMultisetPermutationAllowedSample_head_conditional_first_prob_eq_countWeight_freshList_head_prob`.
- The deterministic bridge from the residual word back to the first-appearance
  list is done for the second position:
  `im05_firstAppearanceList_get_one_eq_filter_ne_head_get_zero` and
  `im05_integerMultisetPermutationFirstAppearanceFreshList_one_eq_allowedSample_first`.
- The two-step probabilistic bridge is done in conditional and joint-atom
  forms:
  `im05_integerMultisetPermutationFirstAppearanceFreshList_second_conditional_prob_eq_countWeight_freshList_second_conditional_prob`
  and
  `im05_integerMultisetPermutationFirstAppearanceFreshList_first_second_prob_eq_countWeight_freshList_first_second_prob`.
- The two-slot marginal omission law is now closed:
  `im05_integerMultisetPermutationFirstAppearanceFreshList_prefix_two_omits_prob_eq_countWeight_freshList_prefix_two_omits_prob`
  and `im05_integerMultisetPermutation_base_finite_law_two`.
- The singleton-deletion projection needed for the conditional side is now
  separated from the stochastic comparison:
  `im05_integerMultisetPermutation_erased_namesBeforeFirst_iff_allowedList_firstAppearance_not_mem_take`
  and
  `im05_integerMultisetPermutation_erased_namesBeforeFirst_prob_eq_countOutside_firstAppearance_not_mem_take`.
  The residual-word version
  `im05_integerMultisetPermutation_erased_namesBeforeFirst_prob_eq_countOutside_namesBeforeFirst`
  is also closed.
- The corrected upper-bound wrappers are in place:
  `paper_im05_lemma4_4_freshList_conditional_comparison_from_integerMultiset_erased_upper_bound`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_erased_upper_bounds_and_scaled_count_limits`,
  and the `..._two` specialization.
- The arbitrary-forbidden-set one-draw marginal law is done as
  `im05_integerMultisetPermutation_countOutside_base_finite_law_one`.

Source-proof warning:

The paper text says that conditioning on `F_j` is "equal" to deleting all
copies of `j` from the finite multiset.  This equality is literal for `k = 1`
but not for nonuniform weights when `k >= 2`: for weights
`i=1, j=2, a=3, b=4` and `k=2`, direct Plackett-Luce calculation gives
`Pr[F_i | F_j] = 0.66477...` while the deleted-`j` process gives `0.675`.
The proof route should therefore target the inequality the paper needs,
`Pr[F_i | F_j] <= Pr[F_i]`, or an upper bound through the deleted-`j`
process, rather than formalizing the source equality as a theorem.

Next useful Lean target:

1. Prove the `k = 2` conditional comparison directly for the raw-count
   recursive fresh-list sampler:
   `pmfConditionalProb μ F_j F_i <= pmfProb μ F_i`.
   The likely proof is a two-draw Plackett-Luce algebra lemma or a small
   negative-dependence lemma for weighted without-replacement top-`k`
   omission events.
2. Use the deleted-`j` projection lemmas above only as an upper-bound bridge,
   not as an equality target, unless the weights are uniform or `k = 1`.
3. Generalize the marginal finite law by induction over length with an
   arbitrary initial forbidden set; the new one-draw forbidden-set law is the
   base case.
4. Generalize the pattern from pairs to length-`r` fresh prefixes.  The likely
   clean route is a finite-prefix vector of names plus a `Nodup`/fresh
   certificate, not repeated ad hoc nested sums.
