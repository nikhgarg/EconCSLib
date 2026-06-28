# Formalization Plan: Quantifying Spatial Under-reporting Disparities in Resident Crowdsourcing

This is the paper-local outside-Lean scratchpad. It records source intake,
mathematical target selection, reusable-library choices, and active proof seams.
It is intentionally more operational than the final validation report.

- Namespace: `LBG24SpatialUnderreporting`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
  - Official version: Nature Computational Science 4, 57-65 (2024), version of
    record published 2023-12-05, DOI `10.1038/s43588-023-00572-6`.
  - Open source version for formalization: arXiv `2204.08620`, v4, revised
    2023-12-06.
  - Local main source cache: ignored PDF
    `papers/LBG24SpatialUnderreporting/source.pdf`; text extracted via
    `mutool` to ignored cache `papers/LBG24SpatialUnderreporting/source.txt`.
  - Local Nature supplementary cache: ignored PDF
    `papers/LBG24SpatialUnderreporting/nature_supplementary.pdf`; text cache
    `papers/LBG24SpatialUnderreporting/nature_supplementary.txt`.
  - `pdftotext` is installed through a MiKTeX wrapper that attempted network and
    home-directory setup; `mutool draw -F txt` produced the reliable main text
    cache.
- Source/version mismatch notes:
  - Main arXiv v4 includes the theorem statements and appendix proofs needed
    for formalization. The Nature supplementary text contains the same Appendix
    B.1/B.2 formal results with compatible numbering.
  - The main Nature article and arXiv text differ in bibliography and packaging,
    but no theorem-level difference has been found in the formal core.
- Complete named-result ledger status:
  - Core theorem inventory extracted from `source.txt` and cross-checked against
    `nature_supplementary.txt`.
  - Empirical tables, posterior summaries, and simulation comparisons are not
    theorem targets except where they instantiate the model equations.
- Formula sanity check:
  - Signs/constants/domains:
    - Poisson count PMF is `exp (-λ(e-s)) * (λ(e-s))^M / M!`; the Lean library
      uses `countLikelihood λ (e-s) M`.
    - Theorem 1 / Theorem 2 require `λ > 0`, `e ≥ s`, and for MLE
      `sum_i (e_i - s_i) > 0`.
    - Zero-inflated likelihood needs `0 ≤ γ ≤ 1`; the paper states the mixture
      formula but does not spell out the parameter bounds at the displayed row.
  - Density vs mass / likelihood-kernel representation issues:
    - Appendix Theorem 2 writes `P(S=t | ...)`, `P(E=t | ...)`, and
      `P(T_j=t_j | ...)` for continuous variables. Lean should encode these as
      density/likelihood-kernel factors, not literal point probabilities.
    - The proof route should expose rate-independent density factors `g` and
      `h_m`, and use Poisson/exponential density algebra for the rate-dependent
      part.
  - Dependency map between named source results:
    - Model setup -> Theorem 1.
    - Lemma 1 -> Proposition 1.
    - Conditions 1/2 + Lemma 2 + Poisson interarrival algebra -> Theorem 2.
    - Theorem 2 restates/proves Theorem 1 in process notation.
    - Theorem 1 -> MLE Eq. (3), Poisson regression Eq. (5)-(6), and
      zero-inflated likelihood Eq. (7).
    - Theorem 1 + stopping-time/window assumptions -> observation-window
      constructions Eq. (33) and Eq. (34).
  - Formula-bearing displayed claims that need derivation, not source-row
    assumptions:
    - Eq. (1)-(2): likelihood factorization and Poisson PMF.
    - Eq. (3): MLE ratio.
    - Lemma 1 observed-rate formula.
    - Theorem 2 Eq. (8) and proof cases Eq. (20), Eq. (26), Eq. (32).
    - Eq. (7): zero-inflated mixture likelihood.
- Named result sanity check:
  - Results that look correct as stated:
    - Theorem 1 / Theorem 2: a valid observation window reduces the
      rate-dependent likelihood to the Poisson count likelihood, modulo
      interpreting continuous terms as densities.
    - Lemma 2: a start time whose distribution is independent of the future
      Poisson path leaves the residual waiting time exponential with rate `λ`;
      this is a Poisson memorylessness/stopping-window lemma.
    - Proposition 1: unique observed incident counts alone confound occurrence
      rate and reporting rate; Lean should prove collision/equal-observed-rate
      examples rather than the informal phrase "not identifiable".
  - Suspected bugs, missing assumptions, or ambiguous wording:
    - Appendix Theorem 2 proof, `M>1` case, printed residual `f(e,s,H,J_M)` at
      `source.txt` lines 2177-2194 and Nature supplement lines 607-624 appears
      algebraically inverted. Eq. (31) has `λ^M exp(-λ(e-s)) * A`; with the
      displayed Poisson PMF, the residual needed for Eq. (32) is
      `A * M! / (e-s)^M`, not `A * (e-s)^M / M!`. This is a proof-formula typo,
      not a failure of Theorem 2, because the theorem statement only needs some
      rate-independent factor.
    - Proposition 1 mixes measure notation `dF(t)` with Lemma 1's density `f`.
      Formalization should either use a density-specialized theorem or a
      measure-level expectation theorem; current plan starts with the
      density/Laplace-transform algebra and a collision theorem.
    - Eq. (33)'s stopping-time/rate-independence premise is described as likely
      for the empirical data. Treat it as an explicit source assumption for
      dataset application, not as a Lean-derived theorem.
- Shared-library reuse checkpoint:
  - Mathlib inspected:
    - `Mathlib.Probability.Distributions.Poisson.Basic` for
      `ProbabilityTheory.poissonMeasure`, `poissonMeasure_real_singleton`,
      `poissonMeasure_real_singleton_pos`, and
      `hasSum_one_poissonMeasure`.
    - `Mathlib.Probability.ProbabilityMassFunction.Binomial` and
      `Mathlib.Probability.Distributions.Binomial` exist for binomial PMFs,
      but no ready Poisson-thinning theorem was found, so the needed
      Poisson-binomial thinning theorem was added to `PoissonProcess`.
    - Mathlib calculus/order modules contain the likely pieces for a future
      global MLE proof: log derivatives, exponential derivatives,
      derivative-sign monotonicity, and `IsMaxOn`/`IsMinOn`.
    - Standard real exponential and finite-sum/product algebra from mathlib via
      `Mathlib.Tactic`.
  - Cslib inspected:
    - No queueing/Poisson-process API found in the workspace.
    - Generic PMF/posterior utilities exist in
      `Cslib/Crypto/Protocols/PerfectSecrecy/PMFUtilities.lean`, but they are
      not a good dependency for this paper unless later Bayesian conditioning
      arguments need them.
  - Optlib inspected:
    - No Optlib checkout or package is present in this workspace.
    - No optimization-specific API is needed for the first theorem core. MLE
      argmax proof should use mathlib calculus/order tools rather than a custom
      optimization API.
  - Existing `EconCSLib` inspected:
    - Existing probability modules cover finite PMFs, kernels, large deviations,
      and ranking/admissions distributions, but no reusable Poisson-process
      likelihood module existed.
    - `EconCSLib.Foundations.Probability.Exponential` provides an exponential
      model API (`Exponential.Model`, tail/CDF/PDF facts) that can support
      Lemma 2's exponential waiting-time statement; the count/no-arrival algebra
      should still flow through `PoissonProcess.noArrivalProb`.
    - New reusable module
      `EconCSLib.Foundations.Probability.PoissonProcess` now supplies Poisson
      count likelihoods, no-arrival/at-least-one probabilities, finite product
      no-arrival algebra, observation windows, count-process law certificates,
      raw-arrival likelihood certificates, and likelihood-factorization
      certificates.
  - API chosen and near-misses:
    - Use mathlib's Poisson PMF as the foundation and expose source-paper
      real-valued formulas through thin `EconCSLib` wrappers.
    - Do not attempt a full sample-path construction of a Poisson process in
      this paper folder. Build reusable algebra and certificate interfaces now;
      later queueing/OR papers can replace certificates with a full
      construction.
- Proof strategy consequences:
  - Source proof route to follow:
    - Encode the Appendix B process-notation theorem as the precise source seam.
    - Prove Poisson PMF/no-arrival/MLE/mixture algebra in Lean.
    - Represent continuous start/end/jump-time factors as densities or
      likelihood kernels.
  - Cleaner Lean route or reusable library route:
    - Theorem 1/Theorem 2 should be proved from an explicit window likelihood
      decomposition whose rate-dependent part is derived by reusable Poisson
      algebra. The paper-facing theorem must expose any process-law or
      density-kernel boundary clearly.
    - Proposition 1 should be a concrete equal-observed-rate/collision theorem
      for the map `Λ * (1 - noReportProbability λ)`; this formalizes
      non-identifiability without requiring a full LLN in the first pass.
  - Major issues already reported to the user:
    - The outside-Lean pass found the Appendix Theorem 2 `M>1` residual typo.
      The theorem target remains the corrected factorization; the final report
      should record this as a proof-formula correction note.

## Source Inventory

- Definitions / formatted paper objects:
  - Incident/reporting process model (`source.txt` lines 216-230): incidents of
    type `θ` arrive with occurrence process parameter `Λθ`; incident `i` is born
    at `t_i`, dies at `t_i + T_i`; reports while active follow a homogeneous
    Poisson process with rate `λθ > 0`; `M_i ~ Poisson(λθ T_i)`.
  - Observed data (`source.txt` lines 231-245): observe only incidents with at
    least one report; for each, observe report count/times and agency actions.
  - Theorem 1 conditions (`source.txt` lines 285-323): start variable
    `S_i ≥ t_i` independent of rate conditional on first report; end variable
    `E_i ≤ t_i + T_i` independent of rate and `S_i` conditional on reports up to
    that time; data includes `S_i`, `E_i`, count `Mtilde_i`, and report times.
  - Condition 1 (`source.txt` lines 1843-1847): conditional density/kernel of
    `S` after first jump is `g`, independent of rate and future path.
  - Condition 2 (`source.txt` lines 1848-1856): conditional density/kernel of
    `E` given jump history is `h_m`, independent of rate; and `E` is
    independent of the realization of `S` given first jump.
  - Poisson regression/log-link Eq. (4)/(5): `λθ = exp(α + βᵀ θ)`.
  - Zero-inflated likelihood Eq. (7): mixture of a structural-zero mass and the
    Poisson count likelihood.
  - NYC observation end Eq. (33): `E_i = min(100 days + S_i, t_i^INSP,
    t_i^WO)`, requiring stopping-time/rate-independence interpretation.
  - Chicago observation end Eq. (34): analogous closure/end-of-study minimum.
- Named lemmas / propositions / theorems / corollaries:
  - Main Theorem 1 (`source.txt` lines 285-323): likelihood factorization
    `L(λ|D_i) = p(Mtilde_i; λ(e_i-s_i)) f(D_i)`.
  - Proposition 1 (`source.txt` lines 1626-1656): unique observed incident count
    does not identify `λθ`; observed rate `Λ'_θ = Λθ (1 - ∫ exp(-λθ t) dF(t))`.
  - Lemma 1 (`source.txt` lines 1660-1770): thinning/observed-process rate
    formula, with nonhomogeneous and homogeneous reporting-rate versions.
  - Appendix Theorem 2 (`source.txt` lines 1839-1868): formal process-notation
    restatement of Theorem 1.
  - Lemma 2 (`source.txt` lines 1873-1969): residual waiting time after valid
    `S` is exponential with rate `λ`.
- Theorem-like displayed claims that are used later:
  - Eq. (2): source Poisson PMF.
  - Eq. (3): non-zero-inflated MLE ratio.
  - Eq. (6): Poisson regression likelihood proportional to count PMF.
  - Eq. (7): zero-inflated likelihood.
  - Eq. (20), Eq. (26), Eq. (32): Theorem 2 proof-case factorizations.
  - Footnote/source passage around `source.txt` lines 4406-4420: after the first
    jump, the shifted process is Poisson with the same rate.

## Initial Proof Strategy

- Main theorem chain:
  - Build `EconCSLib.Foundations.Probability.PoissonProcess`.
  - Paper-level definitions wrap the source formulas: exposure, Poisson PMF,
    unique-observed rate, MLE ratio, zero-inflated likelihood.
  - Prove Proposition 1's non-identifiability as equal observed-rate collisions.
  - Prove Theorem 1/Theorem 2 count-likelihood factorization from an explicit
    corrected likelihood decomposition.
  - Prove Eq. (3), Eq. (6), and Eq. (7) as algebraic consequences of the
    factorization.
- Likely reusable `EconCSLib` seams:
  - Poisson count PMF and no-arrival algebra.
  - Product likelihood over finite observation rows.
  - MLE algebra for products of Poisson count likelihoods, at least as
    likelihood-equivalence/score equations; full global argmax may require
    calculus assumptions.
  - Zero-inflated Poisson mixture likelihood.
  - Later reusable target: sample-path Poisson process with independent
    increments, interarrival densities, stopping windows, thinning, and
    first-jump memorylessness.
- Paper steps that look underspecified or analytically hard:
  - Full measure-theoretic construction of `S`/`E` kernels and conditional
    densities.
  - Lemma 1's thinning plus LLN/steady-state asymptotics.
  - Empirical validity of Eq. (33)/(34) stopping-time assumptions.
  - MLE global argmax when total count is zero or exposure degenerates.
- Formal target map:
  - Rows to fully prove now:
    - Source Poisson PMF Eq. (2).
    - No-report / at-least-one-report probability for homogeneous durations.
    - Proposition 1 collision/non-identifiability theorem.
    - Theorem 1/Theorem 2 corrected likelihood-factorization algebra.
    - Eq. (3) MLE ratio as the stationary point/closed-form estimator under
      positive exposure and positive count assumptions, or at minimum the
      source ratio definition plus its score-equation proof.
    - Eq. (6) Poisson regression likelihood proportionality.
    - Eq. (7) zero-inflated mixture formula.
  - Empirical/descriptive rows out of formal theorem scope:
    - Regression coefficient tables, posterior credible intervals, simulation
      numerical values, and dataset-specific claims.
  - Explicit assumption/certificate boundaries, if any:
    - Full process-law construction behind Conditions 1/2 and Lemma 2 may
      remain as a paper-source process-kernel certificate unless closed by the
      new reusable library.
    - Dataset-specific stopping-time validity for Eq. (33)/(34) is a source
      modeling assumption.
- Planned fallback route if the source proof is too informal:
  - Keep a narrow theorem-shaped process-kernel assumption in
    `Assumptions.lean` for the exact Theorem 2 density decomposition, then prove
    all downstream algebra from that single explicit boundary.
  - Do not put paper-specific assumptions in reusable `EconCSLib`.

## Completion Plan From Current Boundary

The current target is the "enough for this paper" route. We are not trying to
finish a full first-principles continuous-time Poisson/stopping-time library
before closing the paper-facing formalization. Instead, the preferred finite
route consumes explicit observed-window source/density records consisting of:

- `HomogeneousPoissonCountingProcessByLaw`: the reusable, paper-neutral
  homogeneous Poisson increment-law object.
- `Theorem2ConditionSourceModel` and `Theorem2ConditionDensitySourceModel`:
  the paper's rate-independent Condition 1/2 terms `g`, `h_m`, density
  kernels, survival-integral factors, and source-data constructors.
- `Theorem2ObservedWindowCase`: the finite zero/one/multi-report observation
  windows used in Appendix Theorem 2.
- `StoppingObservationWindow`: a new reusable helper proving that the paper's
  `min (S + 100 days, endpoint₁, endpoint₂)` preprocessing rules are stopping
  observation windows once the constituent endpoint rules are supplied as
  stopping times.

From those inputs, Lean proves the displayed likelihood and finite-product
consequences, including finite independent Poisson count-family witnesses and
the collapsed total-count PMF route. The full construction of those finite
records from an all-times continuous process, stopping-window sigma-field
semantics, and the paper's informal Conditions 1/2 remains future reusable
library work, not a blocker for the current paper route.

### Phase 1: finish the paper up to the explicit source-assumption boundary

- Keep all paper-facing finite likelihood rows proved in Lean except the
  construction of `Theorem2ConditionSourceModel` /
  `Theorem2ConditionDensitySourceModel` records from a full continuous-time
  Poisson source process.
- The explicit boundary is source-semantics construction, not likelihood
  algebra: derive the shared homogeneous process law, stopping-window validity,
  and Condition 1/2 source/density records from primitive process assumptions,
  interarrival densities, and no-arrival survival terms.
- Everything downstream of those certificates should remain fully compiled:
  Theorem 1 product decomposition, Appendix B.2 corrected factorization,
  Eq. (2), Eq. (3), Eq. (5)-(7), Proposition 1 homogeneous and finite-duration
  non-identifiability rows, and all zero-inflated likelihood rows.
- Prefer positive-exposure paper-facing statements over raw
  `totalExposure ≠ 0` premises whenever the row exposures are known
  nonnegative.  Current wrappers include the finite observed-window route,
  finite schedule route, source-semantics route, process-law route, and
  process-source-data route.
- Because `PaperInterface.lean` currently exposes 48 paper-facing theorem rows,
  final closeout must run the post-formalization workflow with the stricter
  over-30-row audit path, including row-list synchronization across
  `README.md`, `status.json`, `DependencyDAG.tex`, and
  `FINAL_VALIDATION_REPORT.md`.

### Phase 2: future reusable library needed to eliminate the boundary

- Use GN21 work as reusable engineering support, but not as a direct theorem
  closure.  GN21 contributes useful patterns and lemmas for:
  - measure/a.e. wrapper hygiene via
    `EconCSLib.Foundations.Probability.MeasureInequalities`;
  - reward/time/rate denominator discipline via `ContinuousReward` and
    `RenewalReward`;
  - renewal/strong-law-style wrappers for empirical means and time quotients;
  - CTMC/exponential-clock algebra patterns and source-shaped certificate
    discipline.
- The new paper-neutral library still needed for LBG24 closure is a genuine
  homogeneous Poisson point/counting-process layer:
  - process state with count increments over intervals;
  - independent and stationary increments;
  - exponential interarrival distribution and joint interarrival-density
    kernels;
  - first-jump splitting and memorylessness;
  - no-arrival survival over stopping windows;
  - conditional kernels for the paper's `S` and `E` observation windows under
    Conditions 1/2;
  - optional thinning/LLN support for the full Lemma 1 steady-state route.
    The finite-duration Poisson thinning count law itself is now checked; the
    remaining support is the primitive-process IID/steady-state route into it.
- Expected reuse path:
  - Start from the existing `PoissonProcess` count-likelihood algebra already
    used by LBG24.
  - Reuse GN21's proof style for denominator/domain side conditions and
    source-record auditing.
  - Add only paper-neutral point-process declarations to `EconCSLib`; keep
    LBG24-specific observation-window and source-condition records inside
    `papers/LBG24SpatialUnderreporting`.

## Reusable-Library TODO

- Library APIs to use directly:
  - Mathlib `ProbabilityTheory.poissonMeasure` and its real singleton formula
    for PMF grounding.
  - `EconCSLib.Foundations.Probability.PoissonProcess.countLikelihood`,
    `noArrivalProb`, `atLeastOneArrivalProb`,
    `RawPoissonArrivalLikelihood`, `PoissonLikelihoodFactorization`, and
    `HomogeneousPoissonCountingProcessByLaw`,
    `HomogeneousPoissonCountingProcess`, and `HomogeneousCountProcessLaw`.
  - `EconCSLib.Foundations.Probability.Exponential` for the exponential tail
    interpretation of Lemma 2.
  - Local search of mathlib/cslib found no existing reusable homogeneous
    Poisson point-process, independent-increments, or ordered interarrival
    density construction beyond `poissonMeasure` on counts, so the remaining
    process theorem is real new library work.
- Small reusable lemmas to add now:
  - Done: finite product of Poisson count likelihoods collapsed to total count
    and total exposure, both as a raw likelihood shape and as a single
    total-count Poisson PMF up to a rate-independent residual.
  - Done: finite product of `PoissonLikelihoodFactorization` certificates
    collapsed to one total-count Poisson likelihood.
  - Corrected residual algebra: if a likelihood case has the shape
    `A * rate^M * exp (-(rate * exposure))`, then for positive exposure it
    factors as
    `(A * M! / exposure^M) * countLikelihood rate exposure M`.
  - Zero-inflated Poisson count likelihood helpers and nonnegativity facts.
  - No-arrival/exponential-tail bridge for homogeneous count processes.
  - Done: `NoArrivalKernel.fromWindow` plus
    `HomogeneousCountProcessLaw.windowNoArrivalKernel_likelihood_eq_prob`,
    tying the zero-report window kernel directly to the homogeneous
    count-process law.
  - Done: `noArrivalProb_add_div_noArrivalProb_left`, the reusable
    memoryless-tail ratio algebra behind Lemma 2's residual waiting-time
    argument.
  - Done: reusable ordered-window constructors
    `OrderedOneJumpWindow`,
    `OneInterarrivalTailKernel.fromOrderedWindow`,
    `OrderedFiniteJumpTimeline`, and
    `FinInterarrivalTailKernel.fromWindowJumpTimes`, so paper-local source
    data is assembled from checked observation-window/timeline objects rather
    than arbitrary real gaps and tails.
  - Done: exponential PDF/survival bridges
    `interarrivalDensityKernel_eq_exponential_pdfReal`,
    `OneInterarrivalTailKernel.likelihood_eq_exponential_pdfReal_mul_tail`,
    and
    `FinInterarrivalTailKernel.likelihood_eq_exponential_pdfReal_prod_mul_tail`,
    plus ordered-window specializations that package the nonnegativity proofs.
  - Done: reusable `ObservedArrivalCase` for zero-arrival, one ordered-arrival,
    and finite ordered-arrival observations, with one generic factorization
    theorem from the observed no-arrival/interarrival kernel to the Poisson
    count likelihood. LBG24 now uses this as an audit layer separating
    paper-specific condition residuals from paper-neutral Poisson arrival
    algebra.
  - Done: paper-local one/multi source-data density decompositions, separating
    the rate-independent condition-function residual from the reusable
    arrival kernel before the Poisson-PMF collection step.
  - Done: reusable `HomogeneousArrivalDensityLaw` and
    `HomogeneousPoissonProcessLaw` interfaces, so zero-report count laws and
    one/multi-report ordered arrival-density laws are combined with an explicit
    shared homogeneous Poisson rate. Paper-local bridge theorems now prove the
    zero/one/multi Appendix B.2 factorization from that combined process law.
  - Done: primitive reusable `HomogeneousPoissonCountingProcessByLaw`, with a
    count path, zero-start field, monotone-path field, mathlib
    independent-increment property, and stationary Poisson increment laws.
    The formula-facing `HomogeneousPoissonCountingProcess` and
    `HomogeneousCountProcessLaw` are derived from those `HasLaw` fields. The
    same layer proves finite and natural timeline interval-count independence,
    adjacent interval-count independence, finite-dimensional joint measure/real
    product theorems for adjacent interval-count events, and finite-dimensional
    Poisson count-likelihood product/collapsed-total-count laws.
  - Done: canonical `HomogeneousArrivalDensityLaw` construction from a positive
    homogeneous rate, and `HomogeneousPoissonProcessLaw.withCanonicalArrivalDensity`,
    so LBG no longer assumes the one/multi ordered-arrival density formulas as
    opaque record fields.
  - Done: unified `Theorem2ProcessLawCase` bridge, converting zero/one/multi
    combined-process-law observations into `Theorem2ProcessSourceData` and then
    applying the existing Poisson-PMF factorization.
  - Done: theorem-facing `assumption_theorem2_poisson_process_and_conditions`
    and `Theorem2ObservedWindowCase` layer, so the remaining paper-source
    process/Condition 1/2 boundary is explicit in `Assumptions.lean` and
    listed in `status.json` assumption metadata.
  - Done: direct `Theorem2ConditionSourceModel` and
    `Theorem2ConditionDensitySourceModel` constructors and finite-product
    wrappers, so the preferred paper route no longer has to pass through the
    bundled process-source assumption when proving finite observed-window
    likelihood rows.
  - Done: fixed-function `Theorem2FixedConditionDensitySourceModel`, where
    fixed `g(s)` and `h_m(e)` data construct the rate-indexed density-source
    model and prove rate-independence by reflexivity.
  - Done: Poisson-binomial thinning algebra, including the real
    binomial-thinning mass, the `kept + extra` summand identity, the
    discarded-arrival `HasSum`/`tsum` identity, and the full unshifted
    `HasSum`/`tsum` theorem over original arrival counts.
  - Done: reusable `PoissonThinningCountLaw` certificate and paper-local
    `lemma1FiniteDurationPoissonThinningCountLaw` constructor, isolating the
    remaining stochastic-model premise from the checked thinning algebra.
  - Done: continuous-duration and nonhomogeneous cumulative-intensity Lemma 1
    thinning count-law specializations, plus continuous-duration IID LLN target
    theorem. The human-facing rows now target the continuous source formula
    rather than the finite-duration proxy.
  - Done: binomial-thinning mass and Poisson-thinning summand nonnegativity
    under `0 <= p <= 1`.
  - Done: lightweight continuous-time `IsStoppingTime` and
    `StoppingObservationWindow` API, including deterministic times,
    nonnegative deterministic shifts, pointwise min/max closure, and
    min-censored endpoint window constructors. LBG now applies this to Eq.
    (33)/(34) preprocessing under explicit endpoint stopping-time premises,
    deterministic endpoint specializations, and first-count-arrival
    certificates whose level sets are adapted count-threshold events.
  - Done: reusable `DurationCensoredFirstCountObservationCertificate`, a
    single local finite-observation certificate whose fields imply the
    first-report stopping theorem and the duration-censored stopping
    observation window without a full Kolmogorov/natural-filtration
    construction.
  - Done: the approved local stopping boundary now includes stochastic
    endpoint paper rows and a reusable pathwise projection from
    `StoppingObservationWindow` to deterministic `ObservationWindow`, so the
    certificate reaches the finite observed-window layer without constructing
    a full path-space process.
  - Done: the realized stopping-window bridge now feeds Appendix B.2
    zero/one/multi source-data factorization rows; the NYC/Chicago
    local-count preprocessing rows also prove zero/one/multi-report
    factorization over the certified pathwise exposure.
- Larger reusable components to defer unless needed for closure:
  - Primitive stochastic-process use of thinning:
    connect the checked algebraic theorem and the paper-facing
    finite-duration thinning count row to concrete thinning kernels and
    unit-interval observed-count laws.
  - Full Poisson sample-path process with independent increments, interarrival
    densities, first-jump splitting, and stopping-window likelihood kernels.
    The zero-report no-arrival portion is already connected to the
    primitive counting-process law; the one/multi-report interarrival kernels
    are connected to canonical exponential PDF/survival formulas and packaged
    under `HomogeneousPoissonProcessLaw`. The remaining stochastic theorem
    should supply the compact primitive wrapper/certificate bundle:
    `HomogeneousPoissonCountingProcessByLaw`, fixed paper `g`/`h_m` kernels,
    and the duration-censored stopping-certificate fields for the concrete
    process/endpoints.
  - Done: reusable global Poisson log-likelihood kernel MLE theorem over
    positive rates for positive count and exposure.
- Library-audit risks:
  - Keep `EconCSLib` paper-neutral: no LBG24 theorem numbers, civic-reporting
    terminology, or source-specific observation-window formulas in reusable
    declarations.
  - Certificate APIs in `EconCSLib` are acceptable, but paper-facing theorems
    must either construct certificates from source primitives or mark them as
    explicit paper-local boundaries.

## Execution Checklist

- [x] Download/cache source PDFs and text extracts.
  - Main arXiv PDF, Nature supplementary PDF, and `mutool` text extractions are
    cached under `papers/LBG24SpatialUnderreporting/` and ignored by Git.
- [x] Complete named-result and formula-bearing displayed-claim inventory.
  - Inventory covers Theorem 1, Proposition 1, Lemma 1, Appendix Theorem 2,
    Lemma 2, Eq. (2), Eq. (3), Eq. (5)-(7), Eq. (20)/(26)/(32), and empirical
    observation-window formulas Eq. (33)/(34).
- [x] Fill the formal target map and initial boundary plan.
  - Current boundary candidate has been narrowed from a generic
    `RawPoissonArrivalLikelihood` and collapsed `Theorem2SourceCase` to
    `Theorem2PrimitiveSourceModel` plus the
    `DurationCensoredFirstCountObservationCertificate` route, with lower
    condition-source/density and process-law/source-data rows retained as audit
    layers.
- [x] Build or select reusable library APIs before paper-local wrappers.
  - Added `EconCSLib.Foundations.Probability.PoissonProcess` using mathlib's
    Poisson distribution and the existing exponential module.
- [x] Replace paper scaffold with source-facing Lean definitions and rows.
  - `MainTheorems.lean` and `PaperInterface.lean` now expose the expanded
    paper-facing theorem surface instead of scaffold placeholders.
- [x] Prove all in-scope finite observed-window rows or downgrade them with
    explicit boundary notes.
  - Algebraic and finite observed-window rows build. The remaining
    process/stopping/kernel certificate bundle and full Lemma 1 primitive
    IID/steady-state scope remain explicit future-library boundaries, so the
    paper remains partially formalized rather than closed.
- [x] Update README, status, plan, and validation report for the current
    partial checkpoint.
  - Checkpoint updated 2026-06-28 for a public partial formalization. The
    documents agree that the paper is partially formalized, with downstream
    algebra, primitive-wrapper likelihood rows, finite count-family witnesses,
    and the local stopping-certificate preprocessing route checked. The
    remaining headline obstruction is supplying the compact
    process/stopping/kernel certificate bundle.
  - Final closeout still depends on proving or intentionally retaining that
    process boundary and then rerunning the full post-formalization audit. The
    current review surface is up to date for the partial checkpoint, but it is
    not a full closeout review surface.
- [ ] Run full audits, placeholder/provenance checks, and DAG validation.
  - `lake build LBG24SpatialUnderreporting` passes; full post-formalization
    audit is not yet appropriate while the paper is still partial. Use targeted
    checks for public partial cleanup.
- [x] Record current unresolved source bug, assumption, and library debt.
  - Appendix B.2 `M>1` residual typo is recorded here and in the interim
    validation report; final report should keep it as a proof-formula correction
    note.
  - The remaining source-model debt is the compact certificate bundle:
    homogeneous count-process law, fixed paper `g`/`h_m` kernels, and local
    stopping-certificate fields for the concrete process/endpoints.

## Active Scratchpad

- Current Lean endpoint:
  - 2026-06-27 status checkpoint: paper-local README, plan, validation report,
    and status JSON have been synchronized for the finite observed-window
    boundary.
  - `lake build EconCSLib.Foundations.Probability.PoissonProcess` passed after
    adding the reusable Poisson likelihood module, interarrival/no-arrival
    kernel certificates, jump-time telescoping, ordered-timeline gap/tail
    nonnegativity, strict observation-window exposure, and nonnegativity
    lemmas, plus the Poisson-binomial thinning mass, summand identities, and
    full `HasSum`/`tsum` thinning theorem.
  - `lake build LBG24SpatialUnderreporting` passes after replacing the scaffold
    with real paper-facing rows in `PaperInterface.lean`.
  - New 2026-06-27 targeted progress: reusable `IsStoppingTime` /
    `StoppingObservationWindow` closure lemmas compile, and the paper-facing
    Eq. (33)/(34) preprocessing rows now construct stopping observation
    windows from explicit endpoint stopping-time assumptions.
  - New 2026-06-28 targeted progress: reusable
    `DurationCensoredFirstCountObservationCertificate` compiles as the tight
    library-level certificate for the local primitive-process route: count
    observability plus first-count level sets imply the first-report stopping
    theorem, and the same certificate constructs the 100-day duration-censored
    stopping observation window. The same checkpoint adds stochastic-endpoint
    Eq. (33)/(34) rows, pathwise deterministic observed-window projections,
    and zero/one/multi-report factorization from those certified preprocessing
    windows.
  - The last generated `source_record_audit.json` expands the previous
    configured 63-row review surface into 30 field-level audit items across
    `Theorem2ConditionFunctions`,
    `HomogeneousPoissonCountingProcessByLaw`, the derived formula-facing
    count/process-law interfaces, and canonical arrival-density interfaces,
    with zero recursion failures. The previous Poisson PMF and ordered-arrival
    density formulas are no longer assumed leaves: the count PMF is derived
    from mathlib `HasLaw` increment assumptions, and the ordered-arrival density
    law is constructed canonically from the same positive rate. The
    counting-process boundary explicitly includes monotone paths so
    count-process semantics are not hidden behind natural-number subtraction.
  - The current interface has an expanded finite-record review surface; exact
    row counts await the next dashboard refresh. The covered theorem families
    include Eq. (2), at-least-one-report probability, Lemma 1 continuous-duration formula, finite weighted-average
    mixture identities and bounds, continuous-duration Poisson thinning count
    law, and IID unit-interval LLN routes to the continuous observed rate,
    homogeneous exponential reporting-delay mean, Appendix Lemma 2's
    restricted-start exponential-tail/count-mass collapse, Proposition 1
    homogeneous and finite-duration
    collision cores including positive-premise variants, Theorem 1/Theorem 2
    conditional likelihood decomposition from explicit
    `Theorem2ConditionSourceModel` and
    `Theorem2ConditionDensitySourceModel` records, with audit rows for
    `HomogeneousPoissonCountingProcessByLaw`,
    `assumption_theorem2_poisson_process_and_conditions`,
    `Theorem2ObservedWindowCase`, `Theorem2ProcessLawCase`,
    `Theorem2ProcessSourceData`, reusable `ArrivalKernelCase`, and
    `Theorem2ProcessKernelCase`, corrected Appendix B.2 source-case,
    condition-function, condition source/density model, observed-jump-time,
    ordered-window jump-time, source-data, and process-kernel algebra for
    zero/one/multi-report cases,
    Eq. (3)
    finite-product raw and total-PMF likelihood kernels, score equation, global
    log-likelihood optimality, Eq. (5)-(6), and generic plus
    regression-substituted Eq. (7).
- Exact current mathematical gap for the public partial checkpoint:
  - Need close or explicitly validate the compact
    process/stopping/kernel-certificate boundary behind Theorem 1 / Appendix
    Theorem 2: `HomogeneousPoissonCountingProcessByLaw`, fixed paper `g` and
    `h_m` kernels, and `DurationCensoredFirstCountObservationCertificate`
    fields for the concrete process/endpoints. The min-censoring closure itself
    is now checked, fixed endpoint plus first-count-arrival variants reduce the
    empirical preprocessing boundary, and the fixed-function Condition 1/2
    route removes separate rate-independence proof fields. Shrinking this
    certificate further requires deeper continuous-time process/natural
    filtration library work.
  - Lemma 1 now has checked continuous-duration IID unit-interval LLN and
    Poisson-thinning count-law routes; the remaining strengthening is deriving
    the IID/integrability and one-period-mean premises from a Poisson
    thinning/steady-state model.
- Next bridge lemmas to try after the public partial release:
  - Done: `countLikelihood` algebra for rewriting `λ^M exp(-λE) * A` as
    corrected residual times `countLikelihood λ E M`, including the three
    Appendix B.2 source cases.
  - Done: unique-observed collision theorem for `Λ * (1 - exp(-λT))`, plus
    finite and continuous duration-mixture collision variants.
  - Done: finite product of factorized incident likelihoods.
  - Done: zero-inflated likelihood nonnegativity and case simplifications.
  - Done: generic `ArrivalKernelCase`, process-law
    `observedArrivalCaseLikelihood`, restricted-start Lemma 2 mixture, and
    Lemma 2 count-mass/density-collapse support.
- Informal proof sketch / recurrence / construction:
  - Theorem 2 cases all isolate `λ^M exp(-λ(e-s))` times a residual independent
    of `λ`.
  - Rewriting to the source Poisson PMF requires multiplying the residual by
    `M! / (e-s)^M` for positive exposure.
  - MLE Eq. (3) follows from the product log-likelihood score
    `sum M_i / λ - sum exposure_i = 0`, hence `λ = sum M_i / sum exposure_i`,
    under positive count/exposure and ignoring constants independent of `λ`.
  - The finite product likelihood is now Lean-checked as a reusable collapse to
    total count and total exposure, and the positive-rate log-likelihood
    kernel is now Lean-checked as globally maximized at the displayed MLE.
  - The zero/one/multi-report Theorem 2 source and process-kernel cases are
    now Lean-checked from explicit `g`/`h`/survival-integral/no-arrival/
    interarrival-density kernel factors and from a combined homogeneous process
    law interface, with a unified `Theorem2ProcessLawCase` bridge. The newest
    implementation also exposes reusable `ArrivalKernelCase` and
    `ObservedArrivalCase` factorization underneath each source/process-law
    case; the single-case and finite-product rows now route through
    `Theorem2PrimitiveSourceModel`, with direct
    `Theorem2ConditionSourceModel` / `Theorem2ConditionDensitySourceModel`
    variants retained as audit layers. The remaining process gap is the compact
    homogeneous-count-law/stopping-certificate/fixed-kernel bundle.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
  - Continuous point-probability notation is represented as density/kernel
    likelihood factors.
  - Appendix B.2 `M>1` residual formula appears to have the reciprocal factor
    inverted; Lean will prove the corrected residual factorization and can keep
    a source-literal mismatch row if useful.
- Public partial source-model boundary:
  - Homogeneous Poisson reporting process with `λ > 0`.
  - Fixed paper Condition 1/2 kernels, represented at the preferred interface
    by `Theorem2PrimitiveSourceModel`; lower-level
    `Theorem2ConditionSourceModel`, `Theorem2ConditionDensitySourceModel`, and
    legacy bundle rows remain as audit layers.
  - Dataset-specific stopping-time validity for empirical stochastic endpoint
    choices, when those endpoints are not fixed deterministic times.
- Temporary certificate fields to discharge:
  - The compact process/stopping/kernel certificate bundle if a full Poisson
    sample-path/natural-filtration theorem is not built in this pass.
