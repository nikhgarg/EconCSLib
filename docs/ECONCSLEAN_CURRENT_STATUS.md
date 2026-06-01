# EconCSLib Current Status

Current as of 2026-05-24.

This file is the short repository status front door. Detailed theorem ledgers
live in each `papers/[Paper]/README.md`; historical roadmaps and old orientation
notes are under `docs/archive/`.

## Build Status

Recent checks:

- `lake build EconCSLib` passed after adding the shared asymptotics lemma.
- `lake build MSVV07AdWords` passed after replacing the AdWords paper-facing
  ledger with declaration-level formulas and theorem wrappers.
- `lake build GCG24UserItemFairness` passed during the front-status refresh.
- `lake build Roth82StableMatching` passed after adding Roth certificate
  wrappers for every named result, the source strict-domain Theorem 1
  stable-complete endpoint, the source strict-domain Theorem 2 optimality proof,
  the indexed finite-domain Theorem 4 serial-dictatorship construction, the
  source-domain Theorem 6 DA-completeness/final-active-step proof, the Lemma 2
  strict simple-report minimal first-crossing induction, the Theorem 5
  strict-simple-report/top-rejected-proposer backward-induction truthfulness
  proof, the Corollary 5.1 first-choice-preserving trace coupling with the
  role-reversed side-optimal statement, the strict-profile Theorem 3
  stable-procedure/truthfulness impossibility, the strict-profile Theorem 7
  padded Theorem 3 arbitrary-`k > 1` construction, and closed DA step
  preservation, termination, and stability. The Roth dashboard surface is now
  the compact 27-row `PaperInterface.lean`; ignored local dashboard review logs
  are human-review state, not tracked validation evidence.
- `lake build GS62CollegeAdmissions` passed after adding the cloned-seat
  many-to-one quota theorem, paper-local post-paper audit ledger, and final
  validation report.
- `lake build IM05MarriageHonestyStability` passed after closing the direct
  `k = 2` raw-count/scaled-count Lemma 4.4 negative-correlation route, adding
  reusable without-replacement first-step recurrences, and recording an exact
  `k = 3` counterexample to the published arbitrary-`k` one-man
  negative-correlation claim. It also passes after adding the Algorithm 4.1
  output-certificate surface, abstract strict-preference ordered-list
  existence, arbitrary-start/divorce DA trace scaffolding, and target-exception
  rejection invariant, including finite resumed-run termination and invariant
  preservation.
- `lake build GHW01DigitalGoods` passed after adding the post-paper audit
  ledger and final validation report.
- `lake build EOS07GSP` passed after adding the static locally-envy-free
  equilibrium predicate, stable-assignment bridge, Theorem 7 ranked `B*`
  outcome plus full ordered-values pairwise envy/slot-envy-free/stable-assignment
  support, VCG-tail algebra, canonical finite-tail stable-comparison lower-bound
  support, specialized ordered ranked canonical-tail certificate, and bundled
  constructed-outcome no-positive-transfers/revenue-minimality endpoint, Theorem 8
  scalar/ranked dropout-price algebra including VCG-tail per-click, finite
  `B*` bid, strict finite `B*` threshold certificates, nonempty open clock-region support and concrete not-dropped/dropped state witnesses, ranked strategy iff-at-`B*`, local utility-comparison and local-optimality package, one-step and off-threshold strict best-response payoff wrappers with VCG-tail value-bound bridge and ordered-tail upper bound, plus direct named-strategy PBE existence endpoints, standard `∃!` PBE uniqueness endpoints, pointwise PBE/named-strategy action equivalence, pairwise PBE action uniqueness, direct PBE strategy equality, direct PBE cutoff-rule plus named-strategy cutoff wrappers, exact-drop-at-threshold plus before/after-threshold one-direction behavior, and not-drop iff characterizations, strict PBE no-early-drop/drop-by-value consequences and concrete PBE and named-equilibrium behavior-region witnesses, PBE outcome equality with VCG for every certified PBE strategy, named-strategy VCG outcome, pairwise PBE outcome equality, componentwise PBE slot/payment equality with VCG, named-strategy slot/payment equality with VCG, pairwise PBE slot/payment equality, bundled exact/strict paper-facing PBE conclusion endpoints including cutoff-complement variants and constructed-outcome variants, named-equilibrium paper-facing conclusion endpoints including cutoff-complement variants and constructed-outcome variants, reduced-form dynamic-game scaffold for certificate plumbing including ordered constructed-outcome certificates and direct ordered VCG/named-strategy outcome-quality endpoints plus a one-stop ordered and strict-ordered reduced-form paper conclusions plus a general strict constructed-certificate ordered named-strategy and arbitrary-PBE endpoints plus first-class strict ordered constructed certificates, including reduced-form packaged constructors and arbitrary-PBE endpoints, exact and strict exact finite `B*` dynamic-game certificate boundaries with named-strategy consistency/sequential-rationality projections for extensional and constructed certificates, constructed ranked-`B*` outcome one-stop slot/payment/VCG-tail/payment-interval/individual-rationality/no-positive-transfers support and constructed ranked-`B*` outcome certificate boundaries, constructed-outcome generic PBE certificate constructors, plus generic dynamic PBE certificate constructors and generic unique-PBE/VCG conclusions, and belief-based
  dynamic-game/PBE
  certificate wrapper, one-step-best-response dynamic sequential-rationality
  bridge, and `PostPaperAudit.lean`.
- `lake build PRPKG24AccuracyDiversity DSWG24DiscretizationBias LMMS04FairDivision MBJG25ProducerFairness MSVV07AdWords Roth82StableMatching GHW01DigitalGoods EOS07GSP LOS02CombinatorialAuctions` passed.
- `lake build LMMS04FairDivision` passed after adding Section 3 adaptive
  deterministic two-bit query endpoints, the Theorem 3.1 eventual/asymptotic
  query wrapper, Claim 3.4 branching-potential finite descent, the low-only
  min-load tie-potential descent, the Theorem 3.3 finite value-pair/IP search
  certificate and size-bound wrapper, the exact and bounded-exact
  rounded-allocation concrete-IP bridges and search-optimality wrappers,
  rounded goods-supply weighted accounting, the low-only no-high
  primary-potential preservation lemma, the low-only/strict-high/boundary
  min/max source-branch constructors, domain-restricted Claim 3.4
  lexicographic descent over exact positive-minimum allocations, the
  exact nonempty-positive-goods feasible-domain wrapper, the concrete
  branching-potential feasible-domain specialization, the empty-bundle
  obstruction for the remaining positive-minimum premise, high-good
  source-value-to-index rounding, low-good aggregation into artificial rounded
  goods, combined high/low rounded goods-supply construction, rounded-supply
  IP assignment seams, materialized-supply positive, `L`-bounded, non-top
  strict-smallness, and bounded-allocation concrete-IP wrappers, exact-domain
  Claim 3.4 lifting from the nonempty-positive domain, finite-search existence
  wrappers from feasible value-pair IP certificates, concrete IP certificates,
  bounded materialized-supply allocations, and Claim 3.4 min/max IP
  certificates, exact nonempty-positive Claim 3.4 branch-step discharge,
  no-top materialized-supply Claim-3.4-to-search routing without a raw hstep
  premise including a weighted-supply-average form, finite-search existence
  wrappers for those no-top Claim 3.4 materialized-supply optima, the
  combined-high/low type-assignment-to-search seam, no-owner no-top
  materialized-supply value-pair/type-assignment extraction from exact
  normalization, combined-supply no-top support under the explicit high-good
  rounding margin, source-domain optimizer selection over exact nonempty
  allocations, owner-map construction of a nonempty exact feasible domain,
  owner-map derivation from exact total value and strict item smallness, an
  owner-map materialized-supply-to-search bridge, and the Lemma 3.5
  raw-additive transfer endpoint on top of the
  closed Section 2 and Section 4 support.
- `lake build GLM20DroppingStandardizedTesting EconCSLib.Foundations.Probability`
  passed after closing the concrete standard-normal Mills/hazard-inverse bridge
  and upstreaming paper-neutral RUM noise/contraction/density-product helpers.
- `lake build GLM20DroppingStandardizedTesting.Proposition5SourceFamilyRows`,
  `lake build GLM20DroppingStandardizedTesting.ProofInterface`, and
  `lake build GLM20DroppingStandardizedTesting.PaperInterface` passed after
  adding the GLM20 generated source-family exactly-one-objective row package
  `GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows` and the public
  `PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`
  bridge.  Restart from
  `papers/GLM20DroppingStandardizedTesting/HANDOFF_2026-05-24.md`.

Expected warnings:

- Accuracy/diversity has no current PRPKG-local `sorry` warnings; its open
  continuous-family work is now recorded as explicit source distribution and
  order-statistic assumptions rather than unfinished proof holes.
  Current PRPKG pickup starts from
  `papers/PRPKG24AccuracyDiversity/HANDOFF_2026-05-23_PRPKG_STOPPING_POINT.md`,
  after the Pareto Lemma D.4 gamma-ratio checkpoint and reusable
  `EconCSLib.Foundations.Math.GammaAsymptotics` transfer.
- Some generic matching deferred-acceptance compatibility wrappers and
  manipulation-trace wrappers still expose explicit certificate assumptions in
  `EconCSLib/Markets/Matching/DeferredAcceptance.lean`; Roth's source-domain
  Theorem 2, Lemma 2, Theorem 5, Corollary 5.1, and Theorem 6 routes no longer
  depend on those certificates.

## Paper Status

| Paper folder | Overall status | Current surface |
|---|---|---|
| `papers/MBJG25ProducerFairness` | Formalized with caveat | `PaperInterface.lean` exposes the fixed-model definitions, Theorems 3.1--3.2, Section 4 definitions, Appendix C decomposition, and the documented interior-quality correction for strict variance decrease. |
| `papers/MSVV07AdWords` | Formalized | `PaperInterface.lean` exposes the paper formulas, closed finite and limiting Theorem 8 endpoints, composed finite explicit Section 6/8 extension guarantees including next-price variants, the multiple-slot slot-expansion theorem, the source-shaped page-level top-`n_q` distinct-bidder competitive theorem, the distinct-choice run invariant, the broad feasible-prefix-rule Theorem 9 endpoint, and the integral-prefix Theorem 9 specialization with canonical capped payoff. `ProofInterface.lean` and `PostPaperAudit.lean` retain the exact Section 4 geometric `x*`/`y*` LP certificate, direct Lemma 3 optimizer/upper-bound wrappers, concrete spent-fraction Balance-choice bridges, concrete aggregate small-bids dual-objective accounting, page-level multiple-slot accounting, and auxiliary source-route Lemmas 1--7/Theorem 8 LP certificate helpers as audited proof-route theorem surfaces. Those helpers are not conditional substitutes for the non-conditional theorem-status endpoints. |
| `papers/LMMS04FairDivision` | Partially formalized | Section 2 and Section 4 source-facing finite endpoints are closed. Section 3 has Theorem 3.1 hard-family/counting/adaptive-query endpoints, Graham support, Lemma 3.5 transfer algebra, finite rounded type/value-pair/IP search certificates, concrete IP construction from rounded type assignments and exact/bounded rounded allocations, combined high/low rounded supply construction, combined-supply no-top support under an explicit high-good rounding margin, materialized-supply accounting and no-top Claim-3.4-to-search/type-assignment bridges, Claim 3.4 exact nonempty-positive finite descent with source-domain optimizer selection and owner-map feasible-domain construction, bundled ratio/concrete-IP summaries, two-scale capped rounded-search surfaces separating original grid scale `L0` from rounded average/window scale `LR`, source-average Claim-3.4 discharges into the named source-auto-cap solver obligation, selected-pair/full-IP source-output packages, and compact conditional external-solver packages. Remaining work starts from `papers/LMMS04FairDivision/START_HERE_NEXT_AGENT.md`: instantiate the abstract external solver consequence with a concrete Lenstra/runtime theorem or equivalent machine-model proof, then package the final PTAS/FPTAS complexity statement. |
| `papers/PRPKG24AccuracyDiversity` | Partially formalized | `PaperInterface.lean` exposes exact finite-discrete, exponential, bounded, and Pareto checkpoint layers. The Definition 3/Proposition 5 order-statistic-mean interface is now explicit, with a uniform `[0,1]` bridge from the paper's bottom-indexed `μ(i,a)` convention to the closed uniform top-`k` formula. Proposition 4 now has a conditional continuous-sphere certificate endpoint: the remaining work is the sphere measure/Laplace-principle layer, not the final minimization step. The exponential finite-sample top-`k` order-statistic route is closed; exact bounded and Pareto power-marginal branches now expose reusable scaled-marginal limit certificates in addition to the sequence-limit formulas. Bounded Lemma D.2 has pointwise kernel, gamma coefficient, full/below/above source change of variables, exact source and rescaled splits, bounded-support integrability, finite-support geometric tail bound, scalar tail-negligibility, growing near-zero rescaled bridge, local dominated convergence from CDF power bounds, and the split/dominated bridge closed. The source-assumption boundary for Lemma D.2 now has a monotone bounded-support constructor from the bounded-tail CDF sandwich to the finite split certificate, and Lemma 1 is exposed through the reflected-CDF integral representation. General bounded/Pareto order-statistic derivations and Corollary 1 distribution construction remain open. |
| `papers/GLM20DroppingStandardizedTesting` | Partially formalized | Lemma 1, Proposition 1, Lemma 2, Theorem 1, and Theorem 2 have paper-facing standard-Gaussian source endpoints; Theorem 1 has an explicit low-capacity/interior-selectivity caveat, and Theorem 2's main-text high-skill direction is proved under the extra `subB < subA` assumption that matches the prose but not the literal theorem statement. The appendix crossed-order direction remains documented as a source caveat. Section 5 is the active pause point: Proposition 2 lower-tail/kappa algebra and Theorem 3 Proposition-5 bridges are mostly proved, including the standard-Gaussian Proposition 5 source-family survivor bridge `PaperInterface.proposition5_subFull_objective_bridge`, zero-fallback school-`J2` objective bridge `PaperInterface.proposition5_school2_zero_fallback_objective_bridge`, standard-Gaussian Proposition 5(ii) fixed-law posterior cost-row objective bridge `PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge`, weighted binary adapters `PaperInterface.theorem3_weighted_binary_objectives_from_subFull_and_fullSub_bridges`, `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_subFull_keep_test_and_fullSub_bridge`, and `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`, posterior cost-row Theorem 3 component-table route `PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows_components`, fixed-law component route `PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_components`, zero-fallback fixed-law route `PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_zero_fallback`, equation-(50) zero-fallback fixed-law route `PaperInterface.theorem3_two_school_academic_merit_equation50_fixed_law_posterior_cost_rows_zero_fallback`, cleaned standard-Gaussian alias `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback`, generated-table keep-test public alias `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test` used by `PaperInterface.theorem3_two_school_academic_merit`, base-table keep-test companion `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_j2_keeps_test`, raw-survivor audit alias `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_raw_survivor_merits`, fixed-law row-regularity helper `PaperInterface.theorem3_posterior_cost_row_regularity`, paired low/high helper `PaperInterface.theorem3_posterior_low_high_cost_row_regularities`, and the packaged generated-table row bridge `PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package` over `GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows`, but concrete Bayesian-game applicant-pool/objective row identifications remain. Restart from `papers/GLM20DroppingStandardizedTesting/HANDOFF_2026-05-24.md`. |
| `papers/GN21DriverSurgePricing` | Formalized | `PaperInterface.lean` now exposes a compact 24-row `review_*` human-review surface: Section 2 definitions, Proposition 3.1, Theorem 1, Lemmas 1--10, Remarks 1/3/4, the two paper-facing Theorem 2 clauses, Theorem 4, and the full feasible sequential current-bounds Theorem 3 endpoint. The larger compatibility alias layer remains in `InterfaceAliases.lean`; `PostPaperAudit.lean` and `FINAL_VALIDATION_REPORT.md` record the source-numbered audit surface. Theorem 3 proves positive-mass measurable IC and a.e. accept-all uniqueness by applying Lemma 9 to the surge state first, transporting the measured reward across that a.e. replacement, then applying Lemma 10 with surge fixed at exact accept-all; the full feasible route uses feasible-policy Lemma 9/10 source data directly. The separate zero-mass-dominance lift remains exposed, and Lean documents the current `ℝ` reward-totalization obstruction through state-rate and certificate-impossibility theorems. |
| `papers/LG21TestOptionalPolicies` | Source-model formalization validated | `PaperInterface.lean` is a compact 16-row human-review surface covering Definitions 1--6, Theorem 3.1 optional-reporting/report-required branches, Theorem 3.2 fairness/no-relevance branches, Lemma 4.1, Propositions 4.2--4.3, and Theorem 4.4. `SOURCE_AUDIT.md`, `FINAL_VALIDATION_REPORT.md`, and the template-styled `DependencyDAG.tex` record the post-formalization audit. `lake build LG21TestOptionalPolicies` passes for the split paper modules. The raw arbitrary-policy counterexamples are retained only as scope checks for an overbroad abstraction outside the paper model. |
| `papers/DSWG24DiscretizationBias` | Formalized | `PaperInterface.lean` exposes readable paper definitions with formulas plus direct theorem statements for Theorem 1 and Theorem 2's parts. `PostPaperAudit.lean` retains the exhaustive source-numbered theorem endpoint ledger; `FINAL_VALIDATION_REPORT.md` records the source inventory, proof deviation for the paper's informal source-transformation route, and optional future abstract extension. Theorem 1(i)--(iii), the binary tightness witness, and Theorem 2(i)--(iii) are closed. |
| `papers/Roth82StableMatching` | Formalized | `PaperInterface.lean` exposes the matching definitions and direct statements for Theorems 1-7, Lemmas 1-2, and Corollary 5.1, including strict-profile Theorem 3 and arbitrary-`k` Theorem 7 endpoints. These source-domain endpoints are closed without extra model-certificate assumptions; older generic certificate APIs remain only as compatibility surfaces. `PostPaperAudit.lean` retains source-numbered endpoint aliases; `FINAL_VALIDATION_REPORT.md` records the strict-preference source domain, quota/many-to-one scope note, and proof deviations. |
| `papers/GS62CollegeAdmissions` | Formalized | `PaperInterface.lean` exposes the stable-marriage, complete-marriage, applicant-optimality, and college-quota statements. `PostPaperAudit.lean` retains endpoints for Theorem 1, finite college admissions with quotas via cloned seats, and Theorem 2; these Lean endpoints are closed without extra model-certificate assumptions. `FINAL_VALIDATION_REPORT.md` records that the cached PDF is a scan and local `pdftotext` has no usable theorem-line OCR; this is a source-audit note rather than a formalization caveat. |
| `papers/IM05MarriageHonestyStability` | Waiting for stronger-model pickup with validation issue | The Roth/GS matching preliminaries, Theorem A-D wrappers, Theorem 3.1 summation/asymptotic endpoint, Algorithm 4.2 fresh-list sampler and prefix laws, Lemma 4.2 deterministic/expectation/reciprocal wrappers, Lemma 4.3 ranked-tail product route, Lemma 4.1 variance/Chebyshev bridge, direct `k = 2` Lemma 4.4 route, Lemma 4.4 counterexamples/corrected tail bridge, Section 6 algebra, and a broad corrected Algorithm 4.1 target-divorcing trace/certificate surface are formalized. The paper is paused rather than nearly finished: the hard remaining seams are `im05_Algorithm41SourcePairWitnessCompletionCertificate` for Algorithm 4.1/Theorem 4.1, a repaired tail negative-correlation or tail-variance input plus stable-market wiring for Theorem 3.1, and the concrete Section 6 five-experiment construction for Theorem 3.2. The published arbitrary-`k` one-man negative-correlation step is false for the recursive Plackett--Luce fresh-list sampler at `k = 3`, and the unrestricted finite Lemma 4.4 variance statement is false for arbitrary nonuniform `D^k`; see `LEMMA4_4_COUNTEREXAMPLE_REPORT.md`, `README.md`, `NEXT_AGENT_HANDOFF.md`, and `FINAL_VALIDATION_REPORT.md`. |
| `papers/GHW01DigitalGoods` | Partially formalized | `PaperInterface.lean` exposes the digital-goods auction definitions and direct statements for Sections 4, 6, 7, 8, and 9, but several final endpoints are currently conditional on explicit paper-model certificates rather than derived from primitive source assumptions. The next full-formalization target is to remove or justify the Theorem 8.2 anonymous sorted-bid certificate and the Theorem 9.3 anonymous erased-bid critical-price certificate. |
| `papers/EOS07GSP` | Partially formalized | `PaperInterface.lean` exposes the compact human-facing verifier surface for GSP non-truthfulness, the running GSP/VCG example, the Theorem 7 ranked `B*` conclusion, and the current finite completed-rank Theorem 8 source-extensive terminal-record endpoint. `PostPaperAudit.lean` retains the exhaustive compiling verifier surface for GSP non-truthfulness, running example truthful-GSP Nash/locally-envy-free/stable-assignment checks, GSP/VCG payments and revenue comparison, running-example VCG-equivalent revenue-minimality, static locally-envy-free/stable-assignment bridges, Theorem 7 ranked `B*` outcome plus full ordered-values pairwise envy/slot-envy-free/stable-assignment support, adjacent-to-global no-envy bridge, VCG-tail algebra, canonical finite-tail stable-comparison lower-bound support, candidate `B*` bid/payment nonnegativity and no-positive-transfers support, canonical VCG payment value-bound derivation, all-ranks `B*` bid-order support, specialized ordered ranked canonical-tail revenue-minimality wrappers with explicit comparison-payment and no-positive-transfers premises, bundled constructed-outcome no-positive-transfers/revenue-minimality endpoint under nonnegative values, and Theorem 8 scalar plus full ranked dropout-price algebra including weak/strict interval bounds, rank-indexed strict-click unboundedness, VCG-tail per-click, finite `B*` bid, named finite `B*` threshold strategy/dropout equivalence plus exact not-drop iff cutoff complements and dynamic named-strategy cutoff wrappers, strict no-early-drop/drop-by-value behavior, strict finite `B*` threshold certificates, nonempty open clock-region support and concrete not-dropped/dropped state witnesses, ranked threshold strategy iff-at-`B*`, local utility-comparison and local-optimality package, one-step and off-threshold strict best-response payoff wrappers with VCG-tail value-bound bridge and ordered-tail upper bound, concrete clock/dropout state updates, dropout-record preservation, strategy-consistent step/history/terminal wrappers plus dropout-record step bridge including finite-`B*` step/history dropout-record/threshold bridge, step/history no-new-drop-before-threshold, and terminal active/inactive threshold and terminal strategy-action characterizations plus a bundled terminal-history behavior certificate, cutoff-strategy bridge, exact and strict PBE terminal bridges, and an integrated strict ordered terminal-dynamic PBE terminal-action/dynamic-threshold-record/global-cutoff/VCG-component certificate with field-level local-model agreement, ranked-threshold strategies with clock-monotonicity, exact not-drop iff cutoff complements, and no-early-drop invariants, one-step and finite-history transition invariants, named local-optimality statements, one-step-best-response dynamic sequential-rationality bridge, sequential-rationality-to-one-step/tie-break and local-deviation dynamic and strict ordered source-completion bridges, exact plus strict local-optimality-to-dynamic certificate boundaries, direct named-strategy PBE existence endpoints, standard `∃!` PBE uniqueness endpoints, PBE iff canonical finite `B*` strategy characterizations, pointwise PBE/named-strategy action equivalence, pairwise PBE action uniqueness, direct PBE strategy equality, direct PBE cutoff-rule plus named-strategy cutoff wrappers, exact-drop-at-threshold plus before/after-threshold one-direction behavior, and not-drop iff characterizations, strict PBE no-early-drop/drop-by-value consequences and concrete PBE and named-equilibrium behavior-region witnesses, PBE outcome equality with VCG for every certified PBE strategy, named-strategy VCG outcome, pairwise PBE outcome equality, componentwise PBE slot/payment equality with VCG, named-strategy slot/payment equality with VCG, pairwise PBE slot/payment equality, bundled exact/strict paper-facing PBE conclusion endpoints including cutoff-complement variants and constructed-outcome variants, named-equilibrium paper-facing conclusion endpoints including cutoff-complement variants and constructed-outcome variants, reduced-form dynamic-game scaffold for certificate plumbing including ordered constructed-outcome certificates and direct ordered VCG/named-strategy outcome-quality endpoints plus a one-stop ordered and strict-ordered reduced-form paper conclusions plus a general strict constructed-certificate ordered named-strategy and arbitrary-PBE endpoints plus first-class strict ordered constructed certificates, including reduced-form packaged constructors and arbitrary-PBE endpoints, extensional strategy uniqueness, and concrete ranked-threshold dynamic-game/PBE characterization, constructed ranked-`B*` outcome certificate boundary, reduced-form constructed-outcome certificate wrappers, extensional outcome certificate boundary, exact plus strict exact finite `B*` dynamic-game certificate boundaries, and source-extensive finite-schedule terminal-record checkers with PBE-carried source history and terminality; the narrowed source obligations are concrete belief consistency, local-deviation characterization of source sequential rationality for arbitrary histories, and arbitrary-history generalized-English terminal-record generation. These feed `PaperTheorem8BStarRankedThresholdStrictOrderedLocalDeviationCoreSourceCompletionCertificate`, which derives the sequential-rationality, one-step/tie-break, one-sided, existing source-completion certificates, and paper-facing PBE conclusions. |
| `papers/LOS02CombinatorialAuctions` | Partially formalized | Combinatorial-auction primitives, critical-price support, Theorem 6.1's clique/graph/set-packing reduction layer plus threshold-decision, reduction-closed hardness-transfer, exact-solver, approximation-solver, named abstract NP=ZPP, and randomized-class note wrappers, the sorted-greedy `sqrt(k)` approximation including source blocker/counting and common-bid filtering/add-back, Section 9 threshold support, and average-order greedy truthfulness are formalized; native machine-level NP-hardness, polynomial-time, and randomized-class proofs remain outside the current library. Start future pickup from `START_HERE_NEXT_AGENT.md`. |
| `papers/KR21Monoculture` | Waiting for stronger-model pickup with validation caveat | Theorem 6 concrete continuous RUM endpoint is closed on the normalized score space, Appendix C Theorem 8 is closed, and substantial Mallows/RUM infrastructure is in place. The paper is paused at hard proof-search seams: arbitrary-size Mallows remaining-set dominance for Theorem 4 and RUM paper-scope bridges around Appendix A/Theorem 5, Theorem 7's probability/Fubini layer, and Theorem 2. The README records the Laplacian strict-well-ordering correction and current caveats. |
| `papers/GCG24UserItemFairness` | Formalized | `PaperInterface.lean` exposes the recommendation fairness definitions plus direct Proposition 1, Proposition 2, Theorem 3, and Theorem 4 statements. The paper README/DAG track the appendix lemmas and closed supporting LP certificates. |

## Repository Organization

- Each active top-level paper folder has `README.md`, `DependencyDAG.tex`,
  `MainTheorems.lean`, and `.gitignore`.
- Source PDFs are cached locally in paper folders and ignored by each local
  `.gitignore`.
- Source text caches (`*.txt`) are kept beside the PDFs for one-time
  `pdftotext` extraction and named-statement audits.
- The old aggregate auction folder `papers/AuctionTestOfTime` has been removed.
  Its content now lives either in `EconCSLib/MechanismDesign/Auctions` or in the
  citation-specific paper folders `GHW01DigitalGoods`, `EOS07GSP`, and
  `LOS02CombinatorialAuctions`.
- `papers/EOS07GSP/POST_PAPER_AUDIT_REPORT.md` and
  `papers/EOS07GSP/FINAL_VALIDATION_REPORT.md` record the current
  source-facing closed/open boundary; the folder is not marked final because
  Theorem 8 still has explicit concrete dynamic-game certificate obligations.
  `papers/EOS07GSP/START_HERE_NEXT_AGENT.md` is the current first pickup note
  for the paused Theorem 8 source-history/PBE work; the older
  `papers/EOS07GSP/HANDOFF_2026-05-06.md` remains a detailed declaration
  ledger. The EOS targets currently compile under `lake build EOS07GSP` and
  `lake build EOS07GSP.PostPaperAudit`.
- EOS07GSP Theorem 8 now also has a cold-start reduced-form terminal-dynamic
  checker generated from the strict ordered local model. This closes the
  reduced-form interface check without an external terminal-history input by
  using a quiescent formal-terminal state; it does not replace the source
  generalized-English extensive-form proof or give an auction-completion
  history.
- EOS07GSP Theorem 8 also closes the terminal dropout-record outcome bridge:
  exact finite `B*` terminal records and exact-drop histories imply the
  constructed ranked `B*` outcome, with rank-local and finite-prefix VCG-tail
  payment and `[0, value]` payment-bound wrappers. A strict ordered terminal-dynamic
  certificate can now be augmented by concrete exact-history completion to give
  a single PBE plus terminal-record outcome endpoint, with a finite
  completed-rank variant for finite paper instances. A finite exact-history
  source-completion endpoint packages this with the core source PBE obligations
  to yield unique PBE plus terminal-record conclusions on the completed ranks;
  arbitrary-PBE VCG slot/payment equality is derived from behavioral uniqueness
  plus constructed-outcome agreement rather than treated as a separate source
  obligation. A one-sided source-completion certificate now matches the paper's
  Step 1/Step 2 proof structure by deriving behavioral iff from "drop at or
  after `q`" and "do not drop before `q`"; the terminal-dynamic certificate now
  has a direct bridge to that one-sided paper-proof shape; the sorted
  finite-schedule endpoint
  has a direct one-sided form, and the clock-sorted exact-drop premise has
  named empty/nonempty/singleton/pair helper lemmas for concrete schedule
  checks. A one-stop constructor assembles the finite-schedule core
  source-completion certificate directly from terminal-dynamic, final-state,
  sorted/no-duplicate, and completed-rank inclusion facts. Exact schedules also
  have direct bridges to named finite-`B*` strategy-consistent histories,
  including the clock-sorted/no-duplicate case, and exact schedules now build
  terminal-history behavior certificates from the rank-local check that every
  unscheduled threshold is above the final clock, with a direct
  clock-sorted/no-duplicate constructor; final-clock helper lemmas for empty,
  nonempty, singleton, and pair schedules make these checks concrete; a
  sorted-schedule constructor now also
  assembles the integrated strict ordered terminal-dynamic certificate from the
  dynamic-game certificate and schedule facts, and these compose to a
  finite-schedule core source-completion constructor from dynamic certificate,
  sorted schedule, terminality, and completed-rank data, with a direct
  unique-PBE terminal-record endpoint from the same data. The same sorted
  schedule data also gives a direct unique-PBE endpoint with the full
  terminal/dynamic/ordered-outcome conclusion. The
  ex-post one-sided certificate matches the paper's "best response regardless
  of beliefs" wording by requiring sequential rationality for every belief. The
  single-step exact finite `B*` source-history constructor is available for
  building such finite histories rank by rank, with transitivity and
  append-single wrappers and a list-based exact-drop schedule predicate for
  schedule composition. A sorted-threshold/no-duplicate constructor builds
  schedules from initially active rank lists. Finite schedule terminal-dynamic
  and source-completion endpoints now take an ordered schedule list directly.
  A sorted-schedule core-source wrapper provides the strongest finite source
  boundary with only the narrowed source-PBE obligations. A source-shaped
  local-deviation dynamic game now validates the same source-completion path
  with sequential rationality definitionally equal to the local-deviation
  target and exposes a unique-PBE-with-full-conclusion terminal-dynamic
  endpoint, plus a direct finite exact-schedule local-deviation
  core-source-completion endpoint with terminal-record conclusions and an
  all-scheduled variant that discharges completed-rank inclusion automatically.
  Nonempty finite schedules now also have an append-singleton final-clock
  bridge, so terminality can be audited by comparing unscheduled thresholds to
  the last scheduled threshold rather than to the recursive final-state clock;
  cold-start variants remove the explicit initial-activity premise for the
  canonical no-dropout start state, and singleton/pair cold-start sortedness
  helpers discharge the initial clock inequality automatically. Singleton
  cold-start endpoints now reduce the exact-schedule source check to the
  unscheduled-threshold comparison alone, and pair endpoints reduce it to
  adjacent threshold order, rank inequality, and unscheduled-threshold
  comparisons. General cold-start finite lists can now use adjacent-threshold
  sortedness instead of recursive clock-sortedness, with nil/singleton/cons/pair
  helpers and an append-singleton rule with local boundary-check helpers for
  concrete schedule checks. The threshold-sorted cold-start route now also
  exposes reusable terminal-history behavior, terminal-dynamic, and
  all-scheduled source-completion certificate constructors before the final
  unique-PBE endpoints, plus direct deterministic final-state and
  terminal-history-certificate record and active-iff-unscheduled facts for
  sorted/no-duplicate schedules and their cold-start threshold-sorted
  local-deviation specialization. Exact-history terminal-dynamic certificates
  also expose direct terminal-record
  outcome equality with the constructed successor-tail ranked `B*` outcome,
  plus a unique-PBE endpoint bundling that equality. An all-rank ex-post
  local-deviation exact-history source-completion certificate now packages the
  belief-independent local-deviation source semantics together with exact
  terminal-record generation into one final source-boundary object. Its finite
  exact-history analogue packages the same ex-post local-deviation source
  semantics with exact terminal records and inactive-on-completed evidence for a
  finite completed rank set, then derives the finite unique-PBE terminal-record
  conclusion. Direct local-deviation exact-history and exact-schedule
  constructors instantiate that finite ex-post source object, with an
  all-scheduled variant discharging the completed-subset premise. A direct
  sorted finite-schedule endpoint also starts from the ex-post local-deviation
  certificate and derives the finite terminal-record unique-PBE conclusion
  without requiring a manual conversion through the ex-post one-sided layer;
  its all-scheduled variant removes the completed-subset proof when the
  completed ranks are `scheduledRanks.toFinset`. The cold-start
  threshold-sorted finite schedule route now has a direct ex-post
  local-deviation certificate and unique-PBE terminal-record endpoint, with
  singleton and pair helpers for small concrete schedule checks. The all-rank
  and finite exact-history ex-post source objects now expose direct obligation
  ledgers for the source semantics and terminal exact-history evidence. The
  Theorem 8 dropout-price formula also exposes scalar and ranked
  continuity-in-valuation lemmas, and the exact-history terminal-record route
  now exposes direct utility equality with the constructed successor-tail
  ranked `B*` outcome, including a completed-rank finite analogue. The
  empty-history convention `b_{k+1} = 0` is exposed as scalar and ranked
  dropout-price formulas. Strict adjacent click-through rates now also give
  scalar and ranked injectivity of the dropout price in valuation, with source
  proof-line `q` aliases for continuity, empty history, injectivity, affine
  form, interval/bound facts, and history monotonicity. The
  abstract dynamic-game interface now has a direct utility-equals-VCG bridge
  from same-slot/same-payment fields and from full outcome equality. The
  terminal-record local-deviation dynamic game now makes `outcomeOf` literally
  read terminal dropout records and exposes exact/no-overshoot PBE-to-VCG
  outcome and utility endpoints under the all-inactive terminal-state premise.
  The concrete no-overshoot source-history route is now available from the
  local-deviation core source certificate, with a direct source-shaped
  all-PBE slot/payment, outcome-equals-VCG, and utility-equals-VCG wrapper
  family for generated histories and no-overshoot dropout timing. The same
  generated-history hypotheses now also construct the full source-completion
  certificate and prove the one-stop unique-PBE/full-conclusion theorem from
  the source-shaped reachable/off-path certificate. A terminal-record
  source-shaped dynamic checker now combines that PBE predicate with terminal
  dropout records as `outcomeOf`, with exact/no-overshoot VCG outcome and
  utility endpoints and bundled unique-PBE outcome/utility endpoints under
  all-rank terminal inactivity plus finite
  completed-rank slot/payment and utility endpoints and matching unique-PBE
  packages. It also exposes source-shaped completed-rank paper-formula
  endpoints, with matching unique-PBE wrappers, for the displayed slot/payment,
  VCG-tail accounting, and payment-interval conclusion, including
  threshold-reached variants. The preferred route now
  starts from the no-overshoot terminal-dynamic certificate directly, using the
  annotated finite history instead of a global no-overshoot predicate over all
states. A finite completed-rank variant only requires terminal inactivity on
the completed finite rank set and returns unique PBE plus terminal-record
slot/payment/VCG-tail formulas, with a matching completed-rank utility-equality
endpoint from the same source-shaped no-overshoot data.
  It also exposes finite completed-rank slot/payment and utility endpoints,
  including exact and no-overshoot threshold-reached variants that avoid the
  all-ranks inactivity premise for finite paper checks, plus a cold-start
  threshold-sorted schedule endpoint that maps a displayed nonempty schedule
  directly to completed-rank equality for any PBE in the terminal-record game.
  Singleton and pair terminal-record game endpoints now cover the common small
  displayed schedules with only the local threshold-order, distinct-rank, and
  unscheduled-threshold premises.
  The same terminal-record game now also exposes finite completed-rank
  unique-PBE packages for exact, no-overshoot, threshold-reached, and cold-start
  threshold-sorted routes, including singleton and pair specializations.
  Exact and no-overshoot completed-rank paper-conclusion endpoints also state
  the displayed slot, finite `B*` threshold-payment, VCG-tail, and
  payment-interval formulas for terminal-record game PBEs under ordered
  assumptions, with matching unique-PBE wrappers.
  The cold-start threshold-sorted terminal-record game route now has matching
  displayed-formula and unique-PBE displayed-formula wrappers against the named
  exact-schedule local model, with direct singleton and pair forms for small
  displayed schedules.
  The
  ex-post local-deviation source boundary now exposes direct belief-independent
  sequential-rationality and local-deviation-iff endpoints, including final
  all-rank and finite exact-history source-object lifts for direct audit
  citations without manual `.source` projection, plus direct named-strategy
  local-deviation discharge from the one-step best-response obligation in both
  explicit-belief and nonempty-belief citation forms, together with
  named-strategy "for all beliefs" iff local-deviation endpoints.
  The core, local-deviation,
  ex-post local-deviation, one-step/tie-break, sequential-rationality,
  one-sided, and ex-post source certificates now expose bundled
  obligation-conjunction theorems, so auditors can see exactly which concrete
  belief/sequential-rationality/PBE-behavior facts remain at each source
  boundary. The ex-post local-deviation layer converts to both the
  local-deviation core route and the ex-post one-sided Step 1/Step 2 route,
  and the strict ordered local-deviation dynamic-game checker instantiates
  that ex-post local-deviation boundary directly. That concrete checker now
  also exposes no-extra-premise named-strategy sequential-rationality and
  named local-deviation endpoints by applying the strict one-step
  best-response theorem internally, and it reuses an annotated no-overshoot
  terminal history as the generated history plus exact-drop history for any
  PBE strategy after PBE behavior identifies the strategy with the named finite
  `B*` strategy; the same checker now also derives the completed-rank
  terminal-record paper formulas from that no-overshoot history, with a
  threshold-reached variant that uses final-clock cutoff checks, a matching
  unique-PBE bundle, and all-rank ordered terminal-record paper-conclusion
  endpoints under all-rank terminal inactivity. The ex-post local-deviation
  layer also has direct downstream cutoff, paper-conclusion, and
  unique-PBE-with-conclusion endpoints.
  One-step/tie-break,
  sequential-rationality, one-sided, and ex-post certificates also have direct
  named-strategy PBE, PBE strategy-equality, PBE cutoff-rule, unique-PBE, and
  PBE-to-VCG outcome endpoints without requiring manual conversion through the
  core certificate layer, and full/core/local-deviation certificates expose the
  same direct cutoff-rule endpoint plus named Step 1/Step 2 corollaries; the
  reduced one-step/tie-break, sequential-rationality, one-sided, and ex-post
  routes expose those one-sided corollaries too. Reduced source certificates
  also expose direct compact paper-conclusion endpoints and direct
  unique-PBE-with-compact-terminal-conclusion endpoints, so the audit surface
  no longer requires reviewers to manually compose conversion lemmas through
  the full source-completion certificate. The cold-start
  threshold-sorted finite-schedule route also has an explicitly named
  unique-PBE-with-terminal-record endpoint, and singleton/pair cold-start
  routes have matching terminal-history behavior certificates, direct
  exact-record/active-status facts, terminal-record aliases, and direct
  terminal-record game PBE slot/payment and utility consequences. The
  terminal-record game also has finite completed-rank unique-PBE packages that
  combine uniqueness with slot/payment and utility conclusions, with direct
  singleton and pair forms for small schedules, plus exact/no-overshoot
  paper-conclusion endpoints and unique-PBE wrappers for explicit displayed
  payment formulas, including the cold-start threshold-sorted route and its
  singleton/pair specializations.
  The
  remaining source work is therefore arbitrary-history exact record generation
  for the real source extensive form plus concrete belief consistency and
  instantiation of the source-shaped
  reachable/off-path sequential-rationality predicate for the actual source
  extensive-form game. The predicate is named
  `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement`
  and converts to the existing local-deviation target by
  `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation`.
  The source-completion layer now has
  `PaperTheorem8BStarRankedThresholdStrictOrderedSourceSequentialRationalityCoreSourceCompletionCertificate`;
  its constructor takes concrete belief consistency plus a game-level iff
  against that reachable/off-path predicate, then converts to the existing
  local-deviation core certificate.
  The source-shaped core certificate also now exposes direct named-strategy PBE,
  arbitrary-PBE strategy equality, unique-PBE, and arbitrary-PBE VCG-outcome
  endpoints.
  A standalone
  `paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game`
  checker now exposes direct PBE iff source-shaped, local-deviation, and named
  strategy endpoints for that predicate.
  The compact source-shaped checker now also has the strict ordered
  constructed-outcome certificate
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate`,
  plus direct sorted-schedule full-conclusion endpoints
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`
  and its no-overshoot variant. For that compact game, belief consistency and
  the source-shaped sequential-rationality iff are no longer external
  obligations.
  Annotated no-overshoot terminal histories can now enter the same compact
  source-shaped route directly via
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le`
  and the trace-full
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le`.
  The terminal-record source-shaped route now also has the schedule-level
  endpoint
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`,
  which builds the no-overshoot terminal history and exact finite `B*` records
  directly from sorted no-duplicate schedule data. Its strict ordered
  cold-start variant reduces the schedule check to threshold sortedness,
  no-duplicates, completed-rank membership, and last-threshold unscheduled
  comparisons.
  The source-extensive terminal-record route now puts the generated source
  history and terminality proof inside the PBE predicate itself via
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game`;
  its generic no-overshoot endpoint, threshold-reached variant, sorted
  finite-schedule endpoint, and strict ordered cold-start threshold-sorted
  variant are the current strongest finite paper-checking route exposed in
  `PaperInterface.lean`. The belief-explicit source-extensive checker also now
  has clock-disciplined completed-rank wrappers, with trace-refined versions
  that show the named strategy, generated source history, terminality, and
  exact finite `B*` records.
  A formal overshoot witness now shows bare `StrategyHistory` can record a
  terminal dropout above the finite `B*` threshold, so the exact-record source
  route intentionally uses exact-drop/no-overshoot timing evidence.
  The finite schedule source-completion route now has a direct endpoint
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_clock_sorted_nodup`
  from the source-shaped core certificate plus sorted no-duplicate schedule data.
  Its one-stop variant
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_source_iff_clock_sorted_nodup`
  constructs that certificate from concrete belief consistency and the
  game-level source sequential-rationality iff. The general source-history
  route now also has a direct paper-interface endpoint
  `theorem8_source_iff_histories_no_overshoot_full_conclusion` from concrete
  belief consistency, the source iff, PBE histories, no-overshoot timing, and
  terminal-record outcome/VCG identifications. The no-overshoot
  terminal/dynamic variant
  `theorem8_no_overshoot_terminal_dynamic_source_iff_full_conclusion` drops the
  separate generated-history and global no-overshoot premises when those facts
  are already carried by the terminal certificate; its completed-rank wrappers
  also derive finite-rank inactivity directly from terminal clock thresholds.
  The clock-disciplined source-iff wrapper now builds that no-overshoot
  certificate internally from disciplined terminal histories, with a matching
  completed-rank threshold wrapper.
- Completed paper folders should include a compiling paper-root audit ledger,
  conventionally `PostPaperAudit.lean`, and a `FINAL_VALIDATION_REPORT.md`.
