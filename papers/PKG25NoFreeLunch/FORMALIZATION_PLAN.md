# Formalization Plan: A No Free Lunch Theorem for Human-AI Collaboration

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `PKG25NoFreeLunch`

## Source Inventory

- Source cache:
  - arXiv source downloaded from `https://arxiv.org/e-print/2411.15230`.
  - Ignored local archive: `source_arxiv.tar`.
  - Ignored unpacked TeX: `source_tex/`.
  - Ignored text cache generated from TeX: `source.txt`.
- Definitions / formatted paper objects:
  - Binary classification problem: distribution `D` over `X x {0,1}`.
  - Classifier `Yhat : X -> {0,1}` and 0-1 accuracy.
  - Predictor `P : X -> [0,1]`.
  - Calibration: `Pr[Y = 1 | P(X) = p] = p` for all `p` in the image.
  - Collaboration setting `S = (D, P_1, ..., P_n)` with calibrated predictors.
  - Rounding rule `round(0.5) = 1` and induced individual classifier.
  - Collaboration strategy `C : [0,1]^n -> {0,1}`.
  - Reliability: `acc_C(S) >= min_i acc_i(S)` for all settings.
  - Non-collaboration: there exist `k` and `alpha` such that on `(0,1)^n`,
    `C(p) = round(p_k)` when `p_k != 1/2`, and `C(p) = alpha` when
    `p_k = 1/2`.
  - Correctness/agreement predicates for agents and strategies at an input.
  - Partition-induced calibrated predictors.
- Named lemmas / propositions / theorems / corollaries:
  - Main theorem: every reliable collaboration strategy is non-collaborative.
  - Proposition: linear combinations of collaboration settings.
  - Equivalent theorem restatement: reliability iff the non-collaborative
    two-part condition.
  - Proposition part 1: reliability implies existence of `k` with the
    `p_k != 1/2` deferral property.
  - Lemma counterexample: a violation at coordinate `k` gives a setting where
    agent `k` is strictly more accurate than `C`, and all other agents are at
    least as accurate as `C`.
  - Proposition part 2: once the `p_k != 1/2` deferral property holds, reliability
    forces a fixed `alpha` on the `p_k = 1/2` slice.
- Theorem-like displayed claims that are used later:
  - Accuracy linearity under mixture of settings.
  - Partition-induced predictors are calibrated.
  - In the counterexample construction, the chosen masses force
    `Pr[Y=1 | X in {0,i}] = p_i`.
  - In part 2, mixing `S_1` and `S_2` with `lambda` close to `1` preserves the
    strict inequalities against all non-`k` agents while making `k` beat `C`.

## Initial Proof Strategy

- Main theorem chain:
  1. Build a finite, purely discrete representation of collaboration settings.
     Avoid measure theory initially: model a setting by a finite type `X`,
     positive/normalized masses on `X`, conditional label probabilities
     `eta : X -> Rat/Real`, and calibrated predictors induced by partitions.
  2. Define accuracy in terms of Bayes correctness weights:
     a classifier's expected accuracy is `sum_x mass x * max(eta x, 1-eta x)`
     on correctly classified points plus the complementary value on incorrectly
     classified points. This avoids conditional probability infrastructure.
  3. Prove the finite mixture/linear-combination proposition by disjoint sum of
     finite domains and weighted sums.
  4. Formalize the counterexample lemma exactly as the proof constructs it:
     domain `{0, ..., n}`, partitions `{0,i}` plus singletons, and the two
     mass formulas depending on `C(p)`.
  5. Prove part 1 by contradiction and finite mixture over the `S_k` witnesses.
  6. Prove part 2 with the two finite settings `S_1`, `S_2` and an explicit
     small positive `epsilon` / large `lambda` inequality witness.
  7. Package the equivalent theorem and main theorem.
- Likely reusable `EconCSLib` seams:
  - Finite probability mass functions and weighted-sum accuracy.
  - Disjoint-sum mixture of finite models.
  - Partition-induced calibration for finite distributions.
  - Finite witness construction from a failed dictator/deferral condition.
- Paper steps that look underspecified or analytically hard:
  - The paper writes general distributions and conditional probabilities, but
    every counterexample in the proof is finite. Full closure should be possible
    through a finite-settings theorem plus an embedding statement: finite
    settings are collaboration settings.
  - The proof assumes `n >= 1`; for `n = 0`, `[n]` and `min_i` are not meaningful.
  - `Delta^ell` in the linear-combination proposition should mean nonnegative
    mixture weights summing to one.
  - Part 2's "lambda sufficiently close to 1" should be replaced by an explicit
    finite inequality witness.
- Planned fallback route if the source proof is too informal:
  - First formalize a finite-source version of the theorem. If general
    probability/disintegration becomes expensive, mark the general statement as
    reduced to the finite counterexample embedding rather than building a full
    measure-theoretic calibration API. This should still match the source proof,
    because the adversarial settings it constructs are finite.

## Active Scratchpad

- Current Lean endpoint:
  - `main_no_free_lunch_finite` proves `ReliableFinite C -> NonCollaborative C`.
  - `main_no_free_lunch` proves the source-style endpoint
    `Reliable C -> NonCollaborative C` by restricting source reliability to
    the finite witness settings.
  - `PaperInterface.lean` exposes the completed paper-facing theorem as
    `theorem_main_no_free_lunch`.
- Closed proof components:
  - Finite event mass, label mass, point accuracy, and finite collaboration
    settings.
  - Disjoint-union mixture of finite calibrated settings, with strategy and
    agent accuracy linearity.
  - Proposition 1 counterexample setting over `Option (Fin n)`, including mass
    normalization, calibration, weak dominance for every agent, and strict
    dominance for the failed coordinate.
  - Proposition 1 reliability contradiction by mixing one witness per agent.
  - Proposition 2 first auxiliary setting `S1`, with exact accuracies
    `7/12` for the strategy/agent `k` and `3/4` for non-`k` agents.
  - Proposition 2 second auxiliary setting `S2`, built from two weighted
    Proposition 1 blocks with a special `k` predictor; non-`k` calibration is
    inherited from the block proofs, and `k` calibration is proved by the
    `0`, `1`, and `1/2` level sets.
  - Proposition 2 contradiction using an explicit `7/8` and `1/8` mixture
    rather than an existential "lambda close to 1" argument.
- Remaining process work:
  - Refresh statement-match validator artifacts and human dashboard rows.
  - Dependency DAG PDF has been regenerated and visually inspected.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
  - The paper states general probability spaces, but the proof's separating
    examples are finite. A finite-model proof plus finite-to-general embedding
    is a proof-route specialization, not a source caveat, if the final theorem
    quantifies over all collaboration settings and uses the finite examples only
    to refute non-reliable strategies.
  - The 0-1 "accuracy" displayed near the start uses
    `E |Yhat(X) - Y|`, which is error/loss, while later formulas use accuracy
    as expected correctness, e.g. `E[max{P_i(X),1-P_i(X)}]`. Treat this as a
    source prose/formula typo to check carefully before exposing the definition.
- Genuine paper assumptions:
  - `n >= 1`.
  - Collaboration strategy is deterministic.
  - The non-collaborative definition only constrains `(0,1)^n`; boundary
    predictions `0` and `1` are intentionally exempt.
  - Rounding convention `round(1/2) = 1`.
- Temporary certificate fields to discharge:
  - None were introduced. Finite mass, calibration, and mixture identities are
    derived from explicit formulas.
