# Imported Track Architecture

## Why These Three Papers Fit Together

The imported monoculture, user-item fairness, and diversity-aware recommendation papers all
have a strong finite/discrete entry point.

- monoculture begins with finite rankings and finite expectations
- user-item fairness begins with finite users, finite items, and randomized
  policies
- diversity-aware recommendation begins with finite item types and count allocations

That makes a shared first layer possible:

- `PMF` expectations
- randomized policies
- event-restricted expectations
- classwise/type-symmetric lifting
- finite allocations and representation shares

## Shared Abstractions

### `DecisionCore.FiniteExpectation`

Provides finite expectations and product expectations under `PMF`.

### `DecisionCore.Policy`

Provides randomized policies, per-agent expected scores, aggregate expected
scores, and support combinators.

### `DecisionCore.Conditional`

Provides event-restricted and conditional expectations.

### `DecisionCore.Classwise`

Provides policy lifting along a type/class map and the notion of being constant
on fibers.

### `DecisionCore.Allocation`

Provides finite integer allocations, totals, support, representation shares,
and count-based objectives.

## Paper-Specific Stacks


The monoculture side stays ranking-specific and should remain discrete until the
current Mallows theorem seam is closed.

### User-item fairness

The fairness side stays policy-specific and should remain at the
definition/symmetry/LP-reduction level until the current reduction lemmas are
finished.

### Accuracy-diversity

The diversity-aware recommendation side stays count/objective-specific and should remain
finite and Bernoulli-first before asymptotic order-statistic work.

## Design Rule

Shared reusable mathematics belongs in `DecisionCore`.

Paper-specific mathematics belongs in the corresponding paper namespace.

In particular, Mallows-specific monoculture facts should not be pushed into
`DecisionCore`.
