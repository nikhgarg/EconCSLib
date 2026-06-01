# Tail Variance Exploration

This is a scratch note, not a validation artifact.  It records small numerical
searches after the Lemma 4.4 counterexample showed that unrestricted
negative correlation is false.

## Current Hypothesis

The corrected route should target omission events for women whose popularity
rank is past `2k`, matching the range used by Lemma 4.3.  The known positive
covariance examples live in the top block and disappear when both targets are
restricted to ranks strictly greater than `2k`.

## Small Searches

A brute-force Python enumeration of Plackett--Luce top-`k` ordered prefixes was
run for sorted nonuniform weights.  For each one-man law it computed

```text
p_i  = Pr[one man omits i]
p_ij = Pr[one man omits both i and j]
```

and then checked the all-men covariance

```text
p_ij^n - p_i^n p_j^n
```

for pairs with both zero-based ranks at least `2k`.  It also computed
`Var(Y_tail) / E[Y_tail]` for the selected tail count.

The searches covered:

- `k = 3`, `N = n = 7..12`, tail start `2k`.
- `k = 4`, `N = n = 10..12`, tail start `2k`.
- Random lognormal, Gaussian-log, and coarse plateau weight profiles.

No positive covariance was found in these tail ranges.  The largest observed
variance factors were below `1` in these samples.  Representative maxima:

```text
N=8,  k=3, tail [6,7]:       best C about 0.85
N=10, k=3, tail [6,7,8,9]:   best C about 0.79
N=12, k=3, tail [6..11]:     best C about 0.52
N=10, k=4, tail [8,9]:       best C about 0.73
N=12, k=4, tail [8..11]:     best C about 0.59
```

A later check after the two-draw base was formalized tested a tempting
sufficient condition for the remaining first-step inequality: every residual
one-target omission marginal after a non-target first head is at most the
unconditional first-step marginal.  That pointwise dominance failed in all
sampled tail cases (`n=8,k_res=2`; `n=10,k_res=3`; `n=12,k_res=3`), even though
the first-step NC inequality itself still had no sampled failures.  Do not
try to prove the remaining averaging step through that pointwise bound.

## Formalization Implication

The next formal target should still be the exact tail negative-correlation
input, not only the constant-factor fallback:

```text
∀ idx jdx in tailIdx, idx != jdx,
  Pr[E_idx and E_jdx] <= Pr[E_idx] * Pr[E_jdx]
```

with `tailIdx` a rank block satisfying `2 * k < idx.val + 1`.

If that theorem stalls, the constant-factor variance endpoint is already
available:

```text
paper_im05_lemma4_1_from_tail_variance_factor_and_algorithm4_2_freshList_rank_indices_lemma4_3
```

The count bridge from a rank block into the lower-rank prefix is:

```text
im05_rankIndexBlock_filter_card_le_lowerRankFinset_filter_card
```

For the source's final Lemma 4.3 range, use:

```text
im05_sourceRankTailBlock
paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_multiset_limits_and_lemma4_4
paper_im05_lemma4_1_from_sourceRankTailBlock_algorithm4_2_freshList_full_support_weight_limits_and_lemma4_4
```

## Likely Proof Shape

An induction on `k` is still plausible for the corrected tail statement.  If a
target has one-indexed rank greater than `2k`, then after conditioning on a
first draw different from that target, its residual one-indexed rank is still
greater than `2(k-1)`: deleting one name can reduce the rank by at most one.

This suggests an induction target of the form:

```text
If both targets have at least 2k more-popular/equally-prior names available,
then their omission events in a length-k fresh-list draw are negatively
correlated.
```

The recurrence should split on the first draw and reuse the induction
hypothesis in the residual weight vector.  The remaining algebraic issue is
the first-step averaging inequality that combines the residual negative
correlation bounds.  The existing `k = 2` proof is not structurally reusable
as-is because it expands the two-slot probabilities directly, but its scalar
shape may indicate the inequality needed for the induction step.

## Lean Induction Scaffolding

The following compiled Lean declarations now package the deterministic and
probability recurrences needed for this route:

```text
im05_listPrefixOmits_finCons_succ_iff
im05_finiteWithoutReplacementPMF_listPrefixOmits_succ_prob_eq_sum_head
im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_prob_eq_sum_head
im05_firstStepOmitMarginalSum
im05_firstStepOmitPairProductSum
im05_omissionPairNegativeCorrelation
im05_omissionPairNegativeCorrelation_zero
im05_omissionPairNegativeCorrelation_one_of_ne
im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_negative_correlation_from_first_step
im05_finiteWithoutReplacementPMF_listPrefixOmits_pair_succ_negative_correlation_from_compact_first_step
im05_highWeightAvailableSet
im05_tailDepth
im05_tailDepth_after_insert_of_tailDepth_succ
im05_two_mul_pred_lt_pred_of_two_mul_lt
im05_sourceRankTailBlock_tailDepth
im05_sourceRankTailBlock_after_one_delete_tail_condition
im05_rankPriorIndexSet
im05_rankPriorIndexSet_card
im05_rankPriorIndexSet_erase_card_ge_pred
im05_sourceRankTailBlock_priorIndexSet_erase_card_ge_two_mul_pred
im05_rankAgentByValue_prob_antitone_of_lt
im05_omissionPairNegativeCorrelation_succ_from_tailDepth_first_step
im05_omissionPairNegativeCorrelation_of_tailDepth_firstStep_family
im05_omissionPairNegativeCorrelation_of_tailDepth_positive_firstStep_family
im05_omissionPairNegativeCorrelation_of_tailDepth_twoStep_firstStep_family
im05_omissionPairNegativeCorrelation_two_of_ne
im05_omissionPairNegativeCorrelation_of_tailDepth_twoStepBase_firstStep_family
im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_firstStep_family
im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_positive_firstStep_family
im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_firstStep_family
```

The current strongest reduced target is now only the compact first-step
averaging inequality family over `im05_firstStepOmitPairProductSum` and
`im05_firstStepOmitMarginalSum` for residual lengths at least two.  The generic
two-draw base is closed by `im05_omissionPairNegativeCorrelation_two_of_ne`,
and
`im05_sourceRankTailBlock_omissionPairNegativeCorrelation_from_twoStepBase_firstStep_family`
instantiates the resulting induction for the source block `g / 2, ..., g - 1`.

A later memoized random check of the first-step averaging inequality found many
failures for top-ranked pairs, but no failures in the sampled cases where both
targets were past the parent threshold `2 * (k + 1)`.  This reinforces that the
formal induction statement should be tail-restricted; the first-step inequality
is false as a global weighted-without-replacement claim.

A small exact rational enumeration was also run after the `k = 2` base wrapper
compiled.  It exhaustively checked sorted integer weights in `{1, ..., 5}` for
`n <= 8` and the first nonvacuous parent case `K = 3`, where tail ranks start
at zero-based rank `2K`.  The only nonempty exhaustive case was `n = 8, K = 3`
with 495 target-pair/weight-profile checks; both the compact first-step
inequality and the resulting tail pairwise NC held in every checked case.
This is still only search evidence, not a proof.

A follow-up exact rational check covered a few larger nonvacuous first-step
cases:

```text
n=9,  K=3, weights in {1..4}:  660 checks, no failures
n=10, K=3, weights in {1..4}: 1716 checks, no failures
n=10, K=4, weights in {1..3}:   66 checks, no failures
n=11, K=4, weights in {1..3}:  234 checks, no failures
```

The smallest gaps in these checks occurred on plateau profiles with many equal
high weights and two low-weight tail targets, e.g. `(4, ..., 4, 1, 1)` or
`(3, ..., 3, 1, 1)`.  That suggests the hard formal algebra may be near a
two-level weight-profile boundary, but this is only a heuristic.
