# K=2 Conditional Algebra

This scratch note records the finite two-draw inequality needed for the
corrected Lemma 4.4 route.

Let the raw integer-count weights be `w_u > 0` and let `T = sum_u w_u`.
For distinct `i,j`, write `O = I \ {i,j}`.  Algorithm 4.2 at `k = 2` is the
two-step Plackett--Luce law over distinct names:

```text
Pr[h first, t second] = w_h / T * w_t / (T - w_h),  h != t.
```

The source text claims that conditioning on `j` being absent from the first two
draws equals deleting all copies of `j`.  That equality is false for nonuniform
weights.  The first true finite obligation exposed in Lean was:

```text
Pr[first two omit i | first two omit j]
  <= Pr_uniform_count_vector[2 <= (namesBeforeFirst i).erase j.card].
```

Using the singleton-deletion projection, the right side is the residual
count-vector event after deleting `j`.  If the arbitrary-forbidden marginal law
is proved for `k = 2`, this becomes:

```text
Pr[first two omit i | first two omit j]
  <= Pr_raw_fresh_list_started_with_forbidden_{j}[first two omit i].
```

Direct two-draw formulas:

```text
Pr[A_j] =
  sum_{h != j} w_h / T * (T - w_h - w_j) / (T - w_h)

Pr[A_i and A_j] =
  sum_{h in O} w_h / T * (T - w_h - w_i - w_j) / (T - w_h)

Pr_deleted_j[A_i] =
  sum_{h in O} w_h / (T - w_j) *
    (T - w_j - w_h - w_i) / (T - w_j - w_h).
```

The tempting erased upper bound would therefore be:

```text
  (sum_{h in O} w_h * (T - w_h - w_i - w_j) / (T - w_h))
  / (sum_{h != j} w_h * (T - w_h - w_j) / (T - w_h))
<=
  sum_{h in O} w_h / (T - w_j) *
    (T - w_j - w_h - w_i) / (T - w_j - w_h).
```

This inequality is false in general.  For weights
`w_i = 2, w_j = 1, w_a = 1, w_b = 1`, the left side is
`0.176470...` while the right side is `0.166666...`.  The desired final
negative-correlation inequality still holds in this example because the
unconditional probability of omitting `i` from the first two draws is `0.3`.

So the erased/deleted process is useful as a deterministic projection tool, but
it is not a valid upper bound for the conditional two-draw law.

Closed Lean route:

1. Prove direct negative correlation for hit events:
   `Pr[H_i and H_j] <= Pr[H_i] * Pr[H_j]`, where `H_u` is the event that the
   first two draws hit `u`.
2. Use the exact two-slot atom formula
   `im05_algorithm42FreshList_countWeight_two_hit_both_prob_eq_order_sum` and
   one-target factor formula
   `im05_algorithm42FreshList_countWeight_two_hit_prob_eq_factor`.
3. Split the hazard sums into the paired term plus the outside `{i,j}` terms
   with `im05_sum_if_ne_eq_pair_term_add_outside` and its symmetric version.
4. Bound outside mass by the outside hazard sum using
   `im05_outside_count_div_total_le_sum_div_total_sub`, then apply
   `im05_two_draw_hit_negative_correlation_core_prob_shape`.
5. Complement both hit events with
   `pmfProb_not_and_not_le_mul_of_inter_le_mul` to obtain the actual omission
   theorem
   `paper_im05_lemma4_4_freshList_pairwise_negative_correlation_countWeight_two`.

The final `k = 2` endpoints are
`paper_im05_lemma4_4_freshList_conditional_comparison_countWeight_two`,
`paper_im05_lemma4_4_freshList_conditional_comparison_family_from_scaled_count_negative_correlation_limits_two`,
and
`paper_im05_lemma4_4_variance_le_expectation_from_freshList_scaled_count_negative_correlation_limits_two`.

The attempted general paper route was to replace the two-draw algebra with a
reusable arbitrary-`k` negative-dependence theorem for weighted
without-replacement samples.  That statement is false for the Plackett--Luce
fresh-list sampler at `k = 3`; see `NegativeCorrelationCounterexample.md` and
the Lean scalar witnesses
`im05_plackettLuce_k3_omission_negative_correlation_counterexample_scalar` and
`im05_plackettLuce_k3_conditional_comparison_counterexample_scalar`.
