# Foundations: Probability

Use for `EconCSLib/Foundations/Probability/*`, finite PMFs, expectations,
conditional probability, finite variance, finite Markov kernels/chains/MDPs,
stochastic dominance/couplings, concentration, measure inequalities,
continuous densities, and RUM/noise models.

## Finite PMF and Expectation Seams

- For finite expectation decompositions, prove pointwise identities first, then
  `pmfExp`/`pmfPairExp` sum identities, then the paper-facing equivalence.
  Group by the event or fiber appearing in the paper.
- For probability-delta comparisons, prove the tiny indicator inequality over
  the finite outcome type, then lift it with a generic PMF lemma comparing
  indicator differences.
- For finite independent-sampling concentration, check Mathlib's
  `Probability.Moments.SubGaussian` before proving Chernoff/Hoeffding from
  scratch. A fast reusable seam is: compose independent variables with a
  centering map, use `hasSubgaussianMGF_of_mem_Icc` for bounded variables, and
  expose a paper-facing wrapper over `measure_sum_ge_le_of_iIndepFun`.
- If a broad shared probability file is dirty or being edited by another
  formalization thread, do not spend proof time repairing unrelated theorem
  experiments. Put the needed stable seam in a focused module with distinct
  names, import that module in the paper-facing file, and leave the shared file
  unstaged unless you intentionally own its changes.
- For strict event monotonicity, split the larger event into the smaller event
  plus a residual event and prove positive residual mass from a finite atom
  witness.
- For two-outcome probabilities, first prove `wrong = 1 - correct`, then turn
  `wrong < correct` into `1 / 2 < correct` when that matches the paper proof.
- For pairwise probability monotonicity, define unnormalized `correctWeight`
  and `wrongWeight`, prove their sum is the partition/mass of the relevant
  sample space, and only then normalize. If the paper proof cancels common
  factors to a reduced finite sum, expose a named reduction bridge from actual
  weights to reduced weights; keep the source theorem conditional until that
  bridge is discharged.
- For finite analytic PMF families, prove continuity at the atom level
  `fun theta => ((mu theta) a).toReal`, then lift through finite expectation
  lemmas such as `epsilonContinuousAt_pmfExp_of_atom`.
- For pure PMFs, use lemmas such as `pmfExp_pure`,
  `pmfPairExp_pure_left`, and `pmfPairExp_pure_right` when available.

## Finite Markov Chains and Dynamic Models

- For dynamic EC/platform papers with controlled actions, start with
  `EconCSLib.Foundations.Probability.MDP`: `FiniteMDP`, `FiniteMDP.Policy`,
  `controlledKernel`, `actionValue`, `policyValueStep`, `horizonValue`,
  `optimalStep`, `optimalValue`, and occupancy masses.
- For passive dynamics, use the finite kernel interface in
  `EconCSLib.Foundations.Probability.MarkovChain`: `FiniteMarkovKernel`,
  `transitionProb`, `step`, `iterate`, `expectedNext`, `drift`, `Stationary`,
  `Absorbing`, `ExpectedLe`, and `StochasticallyMonotone`.
- Model policy-induced dynamics with `controlledKernel` when actions matter, or
  as separate kernels over the same finite state type when the paper already
  fixes policies. Compare fixed kernels with `ExpectedLe K L V` for the
  observable or Lyapunov/potential function `V`, then lift to
  `drift_le_of_expectedLe`.
- For queueing, surge, and imbalance papers, define the paper's state type
  first, then a potential such as queue length, imbalance, waiting cost, or
  welfare loss. Prove one-step drift bounds before attempting stationary or
  long-run claims.
- Use `Stationary` only for true steady-state claims. If the paper only needs
  one-step improvement, monotonicity, or a Foster-style drift condition, keep
  the theorem at the `expectedNext`/`drift` layer and record the stationary
  bridge as a separate named assumption or future library seam.
- For monotone dynamics, use `StochasticallyMonotone` when the paper compares
  states under every monotone observable. Use `ExpectedLe` when the comparison
  is only for the paper's specific value function or welfare/potential metric.
- For finite first-order stochastic dominance, use
  `EconCSLib.Foundations.Probability.StochasticDominance`.
  `PMF.FirstOrderLe μ ν` is the expectation order against every monotone
  observable, and `PMF.MonotoneCoupling` is the certificate interface for a
  joint distribution supported on ordered pairs. Use this for admissions,
  recommendation, and platform-policy comparisons before introducing
  paper-specific CDF algebra.
- Keep finite Markov kernels in the probability foundations layer. Paper
  folders should contain only the concrete state encoding, transition law,
  policy parameters, and paper-facing wrappers.

## Measure Inequalities and Bonferroni

- For textbook probability inequalities that appear in a paper, upstream a
  generic statement in `MeasureInequalities.lean` and leave paper wrappers thin.
  Finite union bounds, complement/intersection bounds, and Bonferroni
  truncations are reusable enough for `EconCSLib`.
- For finite Bonferroni proofs, prove the pointwise counting identity first:
  the sum over `powersetCard k` of event indicators equals
  `(activeEvents.card.choose k : ℝ)`. Then use alternating binomial-sum lemmas
  and integrate the pointwise inequality.
- When converting indicator functions to set integrals, introduce explicit set
  names and local equalities for unions/intersections. Avoid relying on one
  large `simp` after unfolding all set notation; prove membership/indicator
  equivalences with `if_pos`/`if_neg` or explicit `Set.mem_iUnion` /
  `Set.mem_iInter` bridges.
- For probability/complement lower bounds, prove the de Morgan set equality
  explicitly, then use `probReal_compl_eq_one_sub` and the finite union bound.
- Keep real-valued probability goals consistently in either `measureProb` or
  `μ.real`; when crossing between them, unfold `Measure.real` locally rather
  than rewriting through large expressions.
- For random-sampling auction proofs where the bad event depends on a
  sample-selected threshold, avoid stopping at a loose union over candidate
  prices if the paper uses a top-prefix argument. Split the proof into:
  deterministic selected-large bridge (often from `alpha * h <= F` plus
  `singlePriceRevenue <= saleCount * h`), selected-bad subset of a fixed
  top-prefix underrepresentation event, finite prefix union bound, and a
  separate geometric-tail lemma. Keep the top-prefix interface explicit until
  its construction is proved, so the remaining paper assumption is auditable.
- When a paper says "top `i` bids" and the rest of the proof only needs that
  threshold winner sets of size at most `i` lie in the prefix, a fast concrete
  model is a sorted `Fin n → ℝ` bid vector with a monotonicity assumption. Define
  the prefix as indices `< i`, prove its cardinality by an equivalence with
  `Fin i`, and prove threshold closure by contradiction using `i + 1` winners.
- For randomized mechanisms whose expectation has a simple finite formula,
  write the expected-payment/revenue double sum directly before introducing
  probability objects. For weighted-pairing-style auctions, the random draw
  "choose `j` with probability proportional to `v_j` and charge `v_j` if
  accepted" becomes a deterministic sum of terms like
  `v_j^2 / (total - v_i)`, which is faster to bound than modeling the sampling
  kernel first.

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
