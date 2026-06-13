# Final Validation Report: User-Item Fairness Tradeoffs in Recommendations

## 1. Human Verdict

- Lean formalization status: partially formalized
- Human dashboard review status: 0/18 rows reviewed; 0 stale; 0 mismatches.
- Main caveat: Premise-source audit is closed; Theorem 3 uses closed
  source-shaped first-half and second-half wrappers rather than algebraic
  bridge certificates.

### Report Metadata

Date: 2026-05-01

### Verdict

The tracked paper-facing formalization for *User-item fairness tradeoffs in
recommendations* is formalized in Lean.

The paper-local status ledger marks no active target remaining, and the targeted
paper build completed successfully. A Lean-file placeholder scan found no real
`sorry`, `admit`, or `axiom` proof gaps in `papers/GCG24UserItemFairness`;
matches were only comment prose.

<!-- transitive-source-premise-audit:start -->
### Transitive Source-Premise Audit

The strengthened recursive source-premise audit does not yet pass for full-status provenance. It follows paper-local wrappers and reusable-library certificate APIs, and treats certificate/source-row/external-boundary premises as full-status blockers unless they are derived internally or routed through validated paper assumptions.

Current result: LP/duality and feasible-support optimality certificates for the Problem 6/11 reduction and misestimation tradeoff rows remain source-boundary proof obligations.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

### Scope Checked

The validation source of truth was the paper folder, not older campaign-level
notes:

- `papers/GCG24UserItemFairness/README.md`
- `papers/GCG24UserItemFairness/DependencyDAG.tex`
- `papers/GCG24UserItemFairness/PaperInterface.lean`
- `papers/GCG24UserItemFairness/MainTheorems.lean`
- the successful targeted Lean build

`PaperInterface.lean` exposes the human-facing definitions and main theorem
statements. `MainTheorems.lean` exposes the full paper-facing wrappers.
Detailed proof work is split across the paper-local LP reduction,
optimization, symmetry, opposing-types, and misestimation files.

## 3. What Has Been Proven

### Results Covered

The formalization covers the paper's tracked named model definitions, supporting
propositions, supporting appendix lemmas, and main paper-facing results,
including:

- recommendation-model user/item fairness definitions and optimization
  predicates;
- Example 1's two-item diverse-preferences toy instance and homogeneous
  tradeoff algebra;
- Proposition 1's symmetric LP-reduction instantiation used downstream;
- Proposition 2's symmetric optimum and sparse-support bridge;
- Appendix C Lemmas 1--2 and Appendix D Lemmas 3--11;
- Theorem 3 price-of-fairness monotonicity through canonical reduction-witness
  wrappers on both halves of the alpha interval;
- Appendix E Lemmas 12--17 and the Problem 11 construction;
- Theorem 4 misestimation/no-fairness and with-fairness source wrappers for both
  possible true cold-start rows.

## 4. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def recommendationUtility | `recommendationUtility` | - Recommendation utility matrix `w_{ij}` for users and items. |
| def rawUserUtility | `rawUserUtility` | - Raw user utility `sum_j w_ij rho_ij`. |
| def normalizedUserUtility | `normalizedUserUtility` | - Normalized user utility `U_i(rho)`. |
| def userFairness | `userFairness` | - User fairness `U_min(rho) = min_i U_i(rho)`. |
| def rawItemUtility | `rawItemUtility` | - Raw item utility `sum_i w_ij rho_ij`. |
| def itemNormalizer | `itemNormalizer` | - Item normalizer `sum_i w_ij`. |
| def normalizedItemUtility | `normalizedItemUtility` | - Normalized item utility `I_j(rho)`. |
| def itemFairness | `itemFairness` | - Item fairness `I_min(rho) = min_j I_j(rho)`. |
| def solvesProblemOne | `solvesProblemOne` | - Problem 1: a policy maximizes user fairness subject to item-fairness level `gamma`. |
| def priceOfFairnessAt | `priceOfFairnessAt` | - Price of fairness at item-fairness level `gamma`. |
| def priceOfFairness | `priceOfFairness` | - Price of maximal item fairness. |
| def priceOfMisestimation | `priceOfMisestimation` | - Price of misestimation for a policy selected on an estimated utility matrix. |
<!-- lean-derived-definitions:end -->

## 5. Named Theorem Statements Checked

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem proposition1_symmetric_lp_reduction | `proposition1_symmetric_lp_reduction` | - Proposition 1: symmetric LP reduction. Type-symmetric original optima are represented by reduced type-level policies. |
| theorem proposition2_symmetric_optimum_exists | `proposition2_symmetric_optimum_exists` | - Proposition 2: under positive utilities, a type-symmetric optimal policy exists for the maximal item-fairness problem. |
| theorem theorem3_price_decreases_first_half | `theorem3_price_decreases_first_half` | Theorem 3 first half: in the opposing two-type model, increasing `alpha` toward `1 / 2` weakly decreases the price of fairness. |
| theorem theorem3_price_increases_second_half | `theorem3_price_increases_second_half` | Theorem 3 second half: in the opposing two-type model, increasing `alpha` away from `1 / 2` weakly increases the price of fairness. |
| theorem theorem4_misestimation_tradeoff_typeZero | `theorem4_misestimation_tradeoff_typeZero` | - Theorem 4 final tradeoff, cold-start user whose true row is the first opposing type: without fairness the misestimation price is at most `1/2`, while with maximal item fairness some estimated optimum has misestimation price above `1 -... |
| theorem theorem4_misestimation_tradeoff_typeOne | `theorem4_misestimation_tradeoff_typeOne` | - Theorem 4 final tradeoff for the second opposing true type. |
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GCG24UserItemFairness --slice all --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| def itemFairness | `itemFairness` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def itemNormalizer | `itemNormalizer` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def normalizedItemUtility | `normalizedItemUtility` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def normalizedUserUtility | `normalizedUserUtility` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def priceOfFairness | `priceOfFairness` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def priceOfFairnessAt | `priceOfFairnessAt` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def priceOfMisestimation | `priceOfMisestimation` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem proposition1_symmetric_lp_reduction | `proposition1_symmetric_lp_reduction` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem proposition2_symmetric_optimum_exists | `proposition2_symmetric_optimum_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def rawItemUtility | `rawItemUtility` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def rawUserUtility | `rawUserUtility` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def recommendationUtility | `recommendationUtility` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def solvesProblemOne | `solvesProblemOne` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem3_price_decreases_first_half | `theorem3_price_decreases_first_half` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The new paper-facing row states the closed first-half Theorem 3 source claim: as alpha moves toward 1/2 in the opposing two-type model, the price of fairness weakly decreases. |
| theorem theorem3_price_increases_second_half | `theorem3_price_increases_second_half` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The new paper-facing row states the closed second-half Theorem 3 source claim: as alpha moves away from 1/2 in the opposing two-type model, the price of fairness weakly increases. |
| theorem theorem4_misestimation_tradeoff_typeOne | `theorem4_misestimation_tradeoff_typeOne` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| theorem theorem4_misestimation_tradeoff_typeZero | `theorem4_misestimation_tradeoff_typeZero` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |
| def userFairness | `userFairness` | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:24Z): The paper statement and Lean-to-TeX draft state the same paper-facing definition or result at comparable granularity. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Paper Assumption Provenance And Modeling Notes

> Strict premise-source audit update (2026-06-12): `assumption_match_llm.json`
> now records per-premise judgments for this paper's `Assumptions.lean`
> ledger. Current result: 34/34 recorded premises are source-matched,
> source-model primitives, or source theorem conditions; 0 remain partial
> boundaries. The old Theorem 3 constrained-optimum bridge certificates were
> removed from the paper-facing interface and replaced by closed source-shaped
> first-half and second-half wrappers.

Every paper-facing theorem premise that is not derived in Lean is routed through
`Assumptions.lean` and checked separately as either a paper/source model
assumption or a paper-statement condition.

| Assumption or condition | Lean declaration | Source location / statement | Validators | Comments |
|---|---|---|---|---|
| Positive utilities | `assumption_positive_recommendation_utilities` | Source model / Theorem 3 setup / Appendix C Lemma 1 | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Covers Proposition 2 and Theorem 3 positive-utility premises. |
| Theorem 3 opposing-type model | `assumption_theorem3_opposing_type_model` | Theorem 3 setup, lines 367-397 and 2078-2086 | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Records the two-type reduced model, positive value vector, and strict value ordering. |
| Theorem 3 first-half alpha domain | `assumption_theorem3_first_half_alpha_domain` | Theorem 3 statement | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | `0 < alpha <= alpha' <= 1/2`. |
| Theorem 3 second-half alpha domain | `assumption_theorem3_second_half_alpha_domain` | Theorem 3 statement | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | `1/2 <= alpha <= alpha' < 1`. |
| Theorem 4 item domain | `assumption_theorem4_at_least_three_items` | Theorem 4 / Appendix E construction | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Nontrivial item geometry for the construction. |
| Theorem 4 true model | `assumption_theorem4_true_model_reduction` | Theorem 4 construction | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Identifies the true model with the two-type source construction. |
| Theorem 4 estimated model | `assumption_theorem4_estimated_model_reduction` | Theorem 4 construction | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Identifies the estimated model with the three-type estimated construction. |
| Theorem 4 displayed reductions | `assumption_theorem4_displayed_reduced_models` | Theorem 4 / Appendix E displayed model definitions | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Pins Lean reductions to the displayed true and estimated matrices. |
| Theorem 4 cold-start wiring | `assumption_theorem4_cold_start_type_wiring` | Appendix E three-type construction | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | The cold-start user is estimated as type 2 and has one of the two true opposing rows. |
| Theorem 4 parameter domain | `assumption_theorem4_parameter_domain` | Theorem 4 statement and Appendix E proof | gpt-5-codex (model; paper_condition; 2026-06-12T00:00:00Z) | Positive epsilon and beta-domain premises. |

### Additional Assumptions Beyond Paper

No additional unverified assumptions remain for the final source Theorem 3 and
Theorem 4 wrappers tracked by the paper README/DAG.

Some declarations expose ordinary mathematical hypotheses that are part of the
formal statement or its intended model, for example finite type representatives
and compatibility assumptions identifying estimated known rows with the true
rows. These are not proof gaps; they are explicit hypotheses in the formalized
model and now have a source-condition ledger.

The main modeling caveat is that the paper's general "finding reduces to an LP"
claim is encoded through paper-local equality-form LP and certificate interfaces
rather than a generic solver-level LP syntax. The final paper-facing wrappers
construct or discharge the needed certificates internally. Auxiliary
selected-BFS/certificate variants that still take explicit inputs are retained
as helper interfaces and are not the closed source theorem wrappers.

## 8. Proof-Strategy Deviations

### Paper-Proof Fidelity

The Lean development follows the paper's named proof architecture closely:
symmetry reduction, sparse support and opposing-types reductions, canonical
pivot/closed-form constructions for Problem 6, mirror symmetry for the second
half of Theorem 3, and the Appendix E Problem 11/cold-start construction for
Theorem 4.

Where the Lean proof differs, the difference is mainly organizational: LP
arguments are factored through auditable certificate structures, and parity,
center, and mirror cases are made explicit as separate lemmas before being
recombined by the final source wrappers.

## 9. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 10. Library Lift Pass

None separately recorded in the existing report.

## 11. DAG Audit

No separate DAG audit note is recorded in the existing report.

## 12. Conditional Results and Remaining Gaps

### Residual Risk

The residual risk is statement-audit risk, not Lean proof risk: a human should
still compare the paper-facing declarations in `MainTheorems.lean` against the
source PDF to confirm that the intended modeling conventions are exactly the
ones desired. The compiled Lean proof itself has no remaining placeholders for
the tracked paper-facing results.

## 13. Suspected Paper Errors or Inconsistencies

### Mistakes or Deviations Found

The main deviation from a literal paper proof is the LP boundary. Instead of
formalizing a general-purpose LP solver/simplex theorem, the proof uses
paper-local equality-form primal/dual certificates, closed-form witnesses,
finite pivot existence, and complementary-slackness-style uniqueness arguments.
This is a proof-method deviation, not an open assumption.

The center-pivot Lemma 15 formula required an explicit convention split: the
source displayed center formula is formalized under a half-LP center-item
convention, while the executable full Problem 11 proof uses the mirrored-policy
identity. The distinction is documented in the README and represented by
separate paper-facing declarations.

Older author-wide status notes were stale for this paper. The paper-local README
and DAG correctly indicate that the final wrappers are closed.

## 14. Validation Checks

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 28 rows; 28 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar
rows: none. Surface audit: not required (30 or fewer paper-facing rows).

Flagged rows: none.

## 15. Final Verdict

- Completion status: formalized.
- Summary: Recommendation fairness propositions and theorem statements are closed under the formal source model, with 34/34 recorded theorem premises source-matched or source-conditioned.
