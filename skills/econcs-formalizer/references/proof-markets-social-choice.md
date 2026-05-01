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
- For Mallows "first mover beats second mover" lemmas, first prove the generic
  collision-loss identity
  `firstMover - independentSecond = sum firstChoiceProb * firstChoiceGapMass`.
  Then use the rank-factorized first-choice and first-choice-gap weights to
  reduce the sum to a positive scalar times the same-human square-weighted
  conditional-gap sum. This is usually faster than expanding the full
  two-ranking expectation directly.
- For Mallows pairwise-correctness monotonicity, separate the paper's
  cancellation-reduced endpoint-position inequality from the later permutation
  bridge. With inverse parameter `q = phi^-1`, correct endpoint placements have
  lower Kendall exponents than incorrect placements, so prove a strict
  cross-product inequality for the reduced weights and then translate the final
  statement as "probability decreases in `q`" rather than "increases in
  `phi`". Keep this rank-only core as a helper, not as a replacement DAG node
  for the paper's full Lemma 8.
- For the full Mallows pairwise-correctness theorem, introduce actual
  `pairCorrectWeight`, `pairWrongWeight`, and `pairCorrectProb` first, with a
  theorem that correct+wrong weights equal the Mallows partition for a
  center-ordered pair. Then prove a `PairPositionReduction`-style bridge saying
  both actual weights are the same positive scale times the reduced
  endpoint-position weights. The final paper wrapper should consume this bridge
  internally; an explicit-input reduction theorem is only conditional progress.
- For sequential best-of-remaining Mallows claims, do not treat pairwise
  correct-ranking monotonicity as automatically proving expected top-of-set
  utility dominance. State the exact remaining-set dominance theorem needed:
  for every feasible hired set, the more accurate ranking law gives weakly or
  strictly higher `expectedBestInSet` on the remaining candidates. Pairwise
  Lemma-8-style declarations are useful inputs, but the source theorem remains
  conditional until the top-of-remaining-set lift is formalized (often via
  subset/restriction rank-factorization or another explicit stochastic
  dominance bridge).
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
