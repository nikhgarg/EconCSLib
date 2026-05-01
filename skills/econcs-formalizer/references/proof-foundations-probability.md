# Foundations: Probability

Use for `EconCSLib/Foundations/Probability/*`, finite PMFs, expectations,
conditional probability, finite variance, continuous densities, and RUM/noise
models.

## Finite PMF and Expectation Seams

- For finite expectation decompositions, prove pointwise identities first, then
  `pmfExp`/`pmfPairExp` sum identities, then the paper-facing equivalence.
  Group by the event or fiber appearing in the paper.
- For probability-delta comparisons, prove the tiny indicator inequality over
  the finite outcome type, then lift it with a generic PMF lemma comparing
  indicator differences.
- For strict event monotonicity, split the larger event into the smaller event
  plus a residual event and prove positive residual mass from a finite atom
  witness.
- For two-outcome probabilities, first prove `wrong = 1 - correct`, then turn
  `wrong < correct` into `1 / 2 < correct` when that matches the paper proof.
- For finite analytic PMF families, prove continuity at the atom level
  `fun theta => ((mu theta) a).toReal`, then lift through finite expectation
  lemmas such as `epsilonContinuousAt_pmfExp_of_atom`.
- For pure PMFs, use lemmas such as `pmfExp_pure`,
  `pmfPairExp_pure_left`, and `pmfPairExp_pure_right` when available.

## Continuous Probability and RUM

- Do not force a finite analogue when the paper theorem is genuinely continuous
  and a direct density/change-of-variables statement is shorter and more
  faithful.
- Split continuous RUM proofs into layers: payoff/certificate algebra over
  rankings, continuous density/change-of-variables inequalities over scores,
  and concrete model instantiation proving support, positive source regions,
  normalization, and score-to-ranking interface facts.
- For continuous distributional inputs that feed a finite theorem over
  rankings, push the measure through the ranking map and convert the finite
  pushforward to a `PMF`. Prove a bridge saying `pmfProb` equals the continuous
  preimage mass.
- For continuous delta inequalities over finite summaries, push the measure
  through the finite summary, apply the finite indicator-difference lemma, and
  pull the result back with a measure-probability bridge.
- For `swapi`/change-of-variables arguments, first prove a reusable
  `withDensity` mass comparison under a measure-preserving measurable
  equivalence and density monotonicity. Then add the paper-local score-geometry
  wrapper proving source regions map into target regions.
- For strict continuous analogues of finite atom witnesses, use a positive
  measure source subset plus a finite source integral. A useful reusable seam is
  a `withDensity` strict comparison lemma with hypotheses like `Measurable D`,
  finite source integral, and positive source measure.
- When a finite certificate seems to require full support of all induced
  rankings, inspect the downstream field actually using it before proving every
  ranking fiber. Often only one strict inequality such as `lambdaOne < 1` is
  needed; for continuous RUMs this can be discharged faster by proving positive
  mass of the exact wrong-choice event and using an identity like
  `wrongProb = 1 - lambdaOne`.
- For concrete continuous support obligations, use explicit open boxes inside
  the target event rather than trying to characterize the whole event. Prove a
  reusable "open box has nonzero volume, and subsets inherit nonzero measure"
  lemma, then instantiate tiny boxes for each lambda source/corrected-top
  region.
- Expose normalized score-law assumptions as the integral equation
  `lintegral D = 1` plus an `IsProbabilityMeasure (mu.withDensity D)` bridge.
  The same equation should discharge finite-source-integral side conditions by
  monotonicity against the full integral.
- Treat ties in real-valued score RUMs explicitly. Either work on no-tie/full
  measure subtypes, prove almost-everywhere ranking-interface lemmas, or state a
  tie-breaking convention and prove score/ranking facts for it.
- After an abstract `withDensity` theorem compiles, add concrete score-space
  utilities for the intended product shape: coordinate projections, measurable
  coordinate swaps, measure-preserving swap lemmas, normalization bridges, and
  finite-source-integral bridges. Align product nesting with Mathlib's product
  measure conventions, for example `(ℝ × ℝ) × ℝ`, so later instantiations do
  not waste time on associativity rewrites.

## Lean Patterns

- Prefer `pmfExp`/`pmfProb` abstractions over hand-expanding `PMF` internals.
- For uniform PMFs over finite spaces, use relabeling lemmas such as
  `pmfExp_uniformPMF_comp_equiv` or `pmfExp_uniformPMF_eq_of_comp_equiv`.
- Open `ENNReal` scope in files that state `ℝ≥0∞` or `∫⁻` expressions.
- When event hypotheses contain abbreviations, normalize each component with
  local equalities before rewriting larger probability goals.
