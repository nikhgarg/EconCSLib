# Foundations: Math

Use for `EconCSLib/Foundations/Math/*`, graph/counting helpers, finite rounding,
finite signs, asymptotics, and interval-crossing arguments.

## Proof Seams

- For sign and inequality arguments, create certificate structures whose fields
  are exactly the nonnegativity, strict positivity, monotonicity, or comparison
  facts needed by the theorem. Prefer sum-level certificates for expectation or
  objective theorems.
- For denominator-cleared finite sums, define the unnormalized numerator, prove
  denominator positivity once, and expose normalized/cleared positivity
  equivalences in both directions.
- For finite exchange arguments, use a generic two-point finite-sum update
  lemma: if two functions differ only at `src` and `dst`, the total sum changes
  by the two pointwise deltas. Then derive first-order inequalities from no
  profitable exchange.
- For finite rounding, split into a reusable no-crossing combinatorial theorem,
  a paper-specific exchange certificate ruling out crossings at optima, and the
  final triangle-inequality or share-error bound.
- For floor/ceiling thresholds around a real optimum, use separate lower and
  upper integer anchors when one anchor cannot serve both roles.
- For analytic crossing proofs, first prove the finite algebra conditionally
  from a named crossing certificate. Then instantiate continuity/limit facts in
  small generic interval modules.
- Do not assume an intermediate-value crossing gives the needed one-sided sign.
  If the proof needs positivity immediately to the right, use a last-nonpositive
  or first-nonnegative compact-interval lemma and state the interval sign-change
  explicitly.

## Lean Patterns

- For singleton indicator sums:

```lean
simpa using
  (Finset.sum_ite_eq' Finset.univ key
    (fun _ => weight))
```

- For sums of divisions over reals, import
  `Mathlib.Algebra.BigOperators.Field` and use `Finset.sum_div`.
- For compact-interval theorems needing mathlib `ContinuousOn`, convert a
  pointwise epsilon-delta interface with a small bridge such as
  `continuousOn_of_forall_epsilonContinuousAt`; keep topology imports local to
  generic interval/analysis modules.
- Keep imports narrow. Prefer specific Mathlib modules over `import Mathlib` in
  new or actively repaired files.
- If a Lean goal is not moving after a few local attempts, extract the exact
  algebraic, finite-sum, relabeling, or monotonicity fact as a named helper
  lemma before returning to the main theorem.
