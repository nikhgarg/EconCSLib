# Negative-Correlation Counterexample

The source proof of Lemma 4.4 claims that for one man's random preference list,
conditioning on woman `j` being absent cannot increase the probability that
woman `i` is absent.  This is true for the closed `k = 0,1,2` formal endpoints,
but it is false for the Plackett--Luce without-replacement sampler at `k = 3`.
The source Theorem 3.1 assumes an arbitrary fixed distribution `D` over women
with every woman assigned positive probability, and defines `D^k` by repeated
draws from `D` with repetitions removed, so the example below is inside the
stated model.

Take six women with weights:

```text
[30, 1, 1, 1, 30, 1]
```

Let `A_0` be the event that woman `0` is omitted from the first three distinct
draws, and let `A_4` be the event that woman `4` is omitted.  Exact enumeration
of the ordered top-three draws gives:

```text
Pr[A_0]       = 6009 / 649264
Pr[A_4]       = 6009 / 649264
Pr[A_0 ∧ A_4] = 1 / 10416
Pr[A_0 | A_4] = 187 / 18027
```

Thus:

```text
Pr[A_0 ∧ A_4] - Pr[A_0] Pr[A_4]
  = 13088125 / 1264631225088 > 0

Pr[A_0 | A_4] > Pr[A_0]
```

Lean records the exact scalar inequalities as:

- `im05_plackettLuce_k3_omission_negative_correlation_counterexample_scalar`
- `im05_plackettLuce_k3_conditional_comparison_counterexample_scalar`

There is also a variance-level counterexample to Lemma 4.4 as stated.  Take
five men and five women, `k = 3`, and weights:

```text
[50, 50, 1, 1, 1]
```

For the two popular women, exact enumeration gives one-man probabilities

```text
p = Pr[A_0] = Pr[A_1] = 461653 / 243700678
q = Pr[A_0 ∧ A_1] = 1 / 176851
```

Let `E_i` be the event that all five men omit woman `i`, and let
`Y = 1_{E_0} + 1_{E_1}`.  Then:

```text
E[Y] = 2 p^5
Var(Y) - E[Y] = 2 q^5 - 4 p^10 > 0
```

Lean records the scalar inequality as:

- `im05_lemma4_4_variance_counterexample_scalar`

This means the paper's Lemma 4.4 proof route cannot be completed faithfully for
arbitrary nonuniform distributions by proving the stated one-man negative
correlation claim; moreover, the variance claim itself is false as stated in
the finite nonuniform model.  The `k = 2` special case remains closed in Lean
through the direct Plackett--Luce algebra route, but the full arbitrary-`k`
theorem needs a corrected source hypothesis or a different probabilistic
statement.
