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
- For finite expectation or revenue lower bounds that keep a disjoint subfamily
  of summands, avoid bespoke nested-sum rewrites. Define an injective map from
  the selected index type into the full index type and use
  `FiniteSum.sum_le_sum_of_injective_nonneg`, with nonnegativity of the full
  summands, to compare the selected sum to the full sum.
- When a proof needs "sort these finitely many objects by score, with ties
  broken arbitrarily", do not leave ranking/injectivity/monotonicity as paper
  assumptions. Build or reuse a finite-ranking helper that maps each object to
  a lexicographic `(score, tie-breaker)` key, enumerates the finite key set with
  `Finset.orderEmbOfFin`, and proves membership, image equality, injectivity,
  and score monotonicity once.
- For finite rounding, split into a reusable no-crossing combinatorial theorem,
  a paper-specific exchange certificate ruling out crossings at optima, and the
  final triangle-inequality or share-error bound.
- For floor/ceiling thresholds around a real optimum, use separate lower and
  upper integer anchors when one anchor cannot serve both roles.
- For real-log or ceiling wrappers around a finite theorem, prove the finite
  theorem first and add the analytic wrapper as a thin layer. Put the
  `Nat.ceil`, `Real.logb`, `rpow_natCast`, and coefficient-rounding facts in
  the wrapper; do not thread analytic side conditions through the combinatorial
  proof. Check exact theorem signatures with `#check`/`exact?` in `/tmp`
  before editing the main file, especially for power monotonicity lemmas whose
  base hypothesis may be `1 <= b` rather than `0 <= b`.
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
- If adding one analytic lemma to an otherwise combinatorial file, try the
  narrow leaf import in a scratch file first. For example, base-log wrappers
  should import `Mathlib.Analysis.SpecialFunctions.Log.Base`, not all of
  Mathlib.
- If a Lean goal is not moving after a few local attempts, extract the exact
  algebraic, finite-sum, relabeling, or monotonicity fact as a named helper
  lemma before returning to the main theorem.
- After `field_simp`, `ring_nf`, or `simp` changes an inequality goal, inspect
  the new target before adding another tactic. These tactics often close the
  goal or convert `0 ≤ a - b` into `b ≤ a`; use `sub_nonneg.mp` /
  `sub_pos.mp` deliberately instead of pushing another algebra tactic by habit.
- For strict finite-sum positivity, name the witness term and prove all other
  terms nonnegative before expanding the whole sum. This avoids broad
  pointwise algebra in the final theorem.
