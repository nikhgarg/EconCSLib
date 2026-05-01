# Markets and Social Choice

Use for `EconCSLib/Markets/*`, `EconCSLib/SocialChoice/*`, matching, fair
division, rankings, Mallows models, and social-choice/ranking papers.

## Matching and Fair Division

- For matching, keep preference, blocking-pair, stability, and algorithmic
  invariants separate. Paper-facing theorem wrappers should call generic
  deferred-acceptance correctness when possible.
- For fair division, reuse bundle/allocation primitives. Prove feasibility,
  marginal-value, and envy/fairness predicates separately before combining them
  in paper wrappers.
- For finite fair-division allocation theorems, first prove a theorem for an
  abstract marginal bound, then instantiate it with the paper's finite maximum
  one-good marginal value.

## Rankings and Mallows

- For rank-weight monotonicity, first prove the PMF/fiber decomposition, convert
  to a pure rank-only weight formula, then prove a generic cleared
  weighted-average lemma from pairwise cross-ratio or prefix dominance.
- If conditioning or deleting a rank creates piecewise weights, prove small
  closed-form below/above/self lemmas and a deletion-sum geometric identity
  before attempting the all-cases theorem.
- For Mallows/ranking proofs, match pairwise decompositions when the paper
  compares `(i,j)` and `(j,i)` top-two events. Prove the top-two expansion,
  define ordered-pair terms, then prove antisymmetric swap identities.
- Keep three Mallows layers separate: denominator-cleared paper sum, top-two
  pair/bracket regrouping, and rank-factorization formulas for first/top-two
  fibers.
- Check strictness and boundary cases before claiming a Mallows theorem is
  assumption-free. State needed interior-parameter and candidate-count
  assumptions at the wrapper.
- For weaker-competition Mallows totals, use the paper's conditional-gap route:
  rank-only conditional gap, adjacent-rank antitonicity, finite MLR
  weighted-average inequality, and the positive same-human square-weighted gap.
- For ranking fibers over `Fin`, normalize first-choice rank `r` with
  `Fin.cycleRange r`; normalize ordered top-two ranks `r < s` with
  `cycleRange r` followed by `cycleIcc 1 s`; normalize swapped top-two ranks
  with `cycleRange s` followed by `cycleIcc 1 (r+1)`.

## Social Choice Probability Bridges

- When only a ranking law changes, rewrite payoff differences as candidatewise
  probability deltas times conditional continuation values. This often turns a
  game/probability theorem into the scalar inequality written in the paper.
- For finite conditional utilities with exactly two possible continuation
  values, use a generic two-outcome expectation lemma
  (`E[f] = Pr[event] * x + (1 - Pr[event]) * y`) before specializing notation.
- For strict probability bounds such as `Pr[event] < 1`, prove positive mass
  outside the event and apply a finite PMF complement lemma.
