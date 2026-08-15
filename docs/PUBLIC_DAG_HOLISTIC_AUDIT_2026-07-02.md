# Public DAG Holistic Audit

- Date: 2026-07-02
- Scope: all 24 papers listed in `papers/human_status.json`
- Public statuses audited: 20 formalized, 4 partially formalized
- Source artifacts checked: `audit/paper_statement_map.json`, `paper_coverage_llm.json`,
  paper-local `status.json`, `docs/DependencyDAG.tex`,
  `docs/DependencyDAG.pdf`, `FINAL_VALIDATION_REPORT.md`, and
  `docs/AGENT_SOURCE_AUDIT.md` when present.

## Method

This pass is a DAG/source-json audit, not a full Lean rebuild. For each public
paper I checked that the DAG artifacts exist, that the rendered PDF is not older
than the TeX source, that the final validation report records DAG evidence, and
that the DAG's paper-facing nodes cover the source-result clusters represented
by the source inventory sidecar. The comparison is cluster-level: formula rows,
source-condition rows, and helper rows do not need standalone DAG boxes when
they are visibly grouped under the relevant paper definition, algorithm, lemma,
proposition, or theorem node.

All 24 public papers have both `docs/DependencyDAG.tex` and
`docs/DependencyDAG.pdf`, and no rendered DAG PDF is stale relative to its TeX
source.

## Summary Findings

- No formalized public paper has a clear theorem-level DAG/source-json mismatch.
- The older report-evidence gaps found in the first pass are resolved as of the
  follow-up edit on 2026-07-02: the affected final validation reports now name
  the DAG artifacts and/or record rendered/visual inspection evidence.
- `KR21Monoculture` now has a `docs/AGENT_SOURCE_AUDIT.md` holistic source-first
  PASS note.
- The four partially formalized papers keep their partial status visible in the
  DAG/status surface. They now also have holistic source-audit notes for the
  declared partial interfaces; these notes do not change their partial status.

## Paper-by-Paper Results

| Paper | Status | DAG/source-json result | Follow-up |
|---|---:|---|---|
| `GS62CollegeAdmissions` | Formalized | PASS. The DAG covers the source definitions, Deferred Acceptance support, Theorem 1, quota wrappers, Theorem 2, and many-to-one admission wrapper. | None. |
| `Roth82StableMatching` | Formalized | PASS. The DAG covers the named theorem/corollary sequence and groups the source's Problem/Definition setup under the model/problem nodes. | None. |
| `GHW01DigitalGoods` | Formalized | PASS. The DAG covers the main theorem and lemma families at the source-result cluster level. | Resolved: final report now records rendered/visual DAG inspection evidence. |
| `MSVV07AdWords` | Formalized | PASS. The DAG covers the source lemmas, algorithms, and Theorems 8/9 through model, algorithm, and theorem clusters. | None. |
| `EOS07GSP` | Formalized | PASS. The DAG covers Definition 4, Lemmas 5/6, Remarks 1-3, Theorems 7/8, and the source example/witness clusters. | None. |
| `GJ19OptimalBinaryRatingSystems` | Formalized | PASS. Apparent missing appendix labels are grouped intentionally: C.1-C.2, B.2-B.3, C.6-C.8, and C.10-C.12 appear as combined DAG nodes. | None. |
| `GGSG19TopThree` | Formalized | PASS. Definitions 1/3 are grouped under the model and K-approval model nodes; the proposition/theorem clusters are visible. | None. |
| `GJ18InformativeRatingSystems` | Formalized | PASS. The DAG is source-consistent at the theorem-family level. | None. |
| `KR21Monoculture` | Formalized | PASS for DAG/source-json coverage. The DAG covers Definitions 1-3, Lemma 1, and Theorems 1-9 at the paper-result level. | Resolved: `docs/AGENT_SOURCE_AUDIT.md` added with a completed source-first holistic PASS note. |
| `LG21TestOptionalPolicies` | Formalized | PASS. The DAG covers Definitions 1/6, Lemma 4.1, Propositions 4.2/4.3, and Theorems 3.1/3.2/4.4. | Resolved: final report explicitly names `DependencyDAG.tex` and `DependencyDAG.pdf`. |
| `GN21DriverSurgePricing` | Formalized | PASS. Lemmas 7-8, Lemmas 9-10, and Remarks 1/3/4 are intentionally grouped; the main theorem and proposition nodes are visible. | Resolved: final report explicitly names `DependencyDAG.tex` and `DependencyDAG.pdf`. |
| `DGJ24OptimalStrategiesRCV` | Formalized | PASS. The DAG covers the source result clusters for the RCV/STV model, Algorithms 1-7, Proposition 2.1, Theorems B.1/3.1/3.2/5.4, Lemmas B.2/C.1, and Propositions 3.3/3.4/5.3/5.5/5.6. Algorithm 6 and Definition C.2 are covered by the `Algorithms 4--6` candidate-reduction/strict-support cluster rather than separate boxes. | None. |
| `PRPKG24AccuracyDiversity` | Formalized | PASS. The DAG covers the definition/example/corollary/proposition/theorem source clusters; source problem rows are grouped into the model layer. | None. |
| `GCG24UserItemFairness` | Formalized | PASS. The DAG covers Problem 1/6/11, Example 1, Lemmas 1-17, Propositions 1/2, and Theorems 3/4. | Resolved: final report names DAG artifacts and records rendered/visual inspection evidence. |
| `PKG25NoFreeLunch` | Formalized | PASS. Source definitions are grouped under `Definitions`; Proposition 6 is the `Linear Combination` node; Propositions 7/9 and Lemma 8 are represented inside the Proposition 2 strategy-subcase cluster. | None. |
| `DSWG24DiscretizationBias` | Formalized | PASS. The DAG covers the paper's Theorem 1/Theorem 2 result clusters and source-model setup. | None. |
| `MBJG25ProducerFairness` | Formalized | PASS. The DAG covers Theorems 3.1/3.2 and the producer-fairness model clusters. | Resolved: final report names DAG artifacts and records rendered/visual inspection evidence. |
| `DGD26AdmissionsPredictability` | Formalized | PASS. The DAG is source-consistent at cluster level: the Appendix 0-instability definition is grouped under `Zero Instability Chain`, and the main instability/variability/queue result clusters are visible. | None. |
| `GGRS26CombattingGerrymanderingRCV` | Formalized | PASS. The DAG covers Proposition 1 and Lemma C.1 source clusters. | Resolved: final report records rendered/visual DAG inspection evidence. |
| `DGJ26PracticalDynamicsRCV` | Formalized | PASS. The DAG covers Proposition 1, Proposition 2, Theorem 2.1, Theorem 2.2, Algorithms 2-4, and the ballot/support/candidate-removal source layers. Definition B.1 strict support is grouped under the support/removal model layers rather than a separate box. | None. |
| `LOS02CombinatorialAuctions` | Partially formalized | PASS for partial status. The DAG shows the formalized source clusters and does not overclaim full closeout. | Resolved for current partial status: final report records DAG evidence and `docs/AGENT_SOURCE_AUDIT.md` added; full closeout still requires native complexity infrastructure. |
| `LMMS04FairDivision` | Partially formalized | PASS for partial status. The DAG keeps the partial source boundaries visible and does not overclaim full closeout. | Resolved for current partial status: final report records DAG evidence and `docs/AGENT_SOURCE_AUDIT.md` added; full closeout still requires fixed-dimension IP runtime infrastructure. |
| `GKGMM19IterativeLocalVoting` | Partially formalized | PASS for partial status. The DAG correctly marks the SSGM convergence boundary and partial paper status; `docs/AGENT_SOURCE_AUDIT.md` records that the broad source-semantics clusters are the intended partial-paper view. | Resolved for current partial status; before marking fully formalized, prove the SSGM convergence boundary and either expand DAG nodes or record explicit closeout coverage for every source-numbered cluster. |
| `LBG24SpatialUnderreporting` | Partially formalized | PASS for partial status. The DAG covers Lemmas 1/2, Proposition 1, and Theorems 1/2 without overclaiming completion. | Resolved for current partial status: final report records DAG evidence and `docs/AGENT_SOURCE_AUDIT.md` added; full closeout still requires discharging or explicitly accepting the remaining source-model/process boundaries. |

## Resolved Follow-Up List

1. Added a completed `docs/AGENT_SOURCE_AUDIT.md` for `KR21Monoculture`.
2. Added or tightened final-report DAG evidence for:
   `GHW01DigitalGoods`, `LG21TestOptionalPolicies`,
   `GN21DriverSurgePricing`, `GCG24UserItemFairness`,
   `MBJG25ProducerFairness`, `GGRS26CombattingGerrymanderingRCV`,
   `LOS02CombinatorialAuctions`, `LMMS04FairDivision`, and
   `LBG24SpatialUnderreporting`.
3. Added holistic source-audit notes for `LOS02CombinatorialAuctions`,
   `LMMS04FairDivision`, `GKGMM19IterativeLocalVoting`, and
   `LBG24SpatialUnderreporting`, including an explicit note that
   `GKGMM19IterativeLocalVoting` uses broad source-semantics clusters as the
   intended partial-paper view.

## Remaining Future Closeout Boundaries

These are not current DAG/source-json documentation failures. They are the
known mathematical or library boundaries that keep the partial papers partial:

- `LOS02CombinatorialAuctions`: native computational-complexity infrastructure.
- `LMMS04FairDivision`: fixed-dimension integer-programming runtime
  infrastructure.
- `GKGMM19IterativeLocalVoting`: reusable SSGM convergence theorem, followed by
  expanded or explicitly closed DAG coverage for every source-numbered cluster.
  Two prerequisites were identified on 2026-08-15 and are recorded in that
  paper's `FINAL_VALIDATION_REPORT.md` section 5: the Theorem 1 and
  Proposition 2 boundary certificates carry no projected-SSGM trace, and
  `ILVEnvironment.convergesWithProbabilityOne` has no almost-sure semantics.
  Both must be fixed before the boundary can be discharged. The paper's two
  inconsistent `axiom` declarations were removed on the same date: Appendix
  Theorem 4 is now proved, and the SSGM boundary is an explicit premise.
- `LBG24SpatialUnderreporting`: discharge or explicitly accept the remaining
  source-model/process boundaries.
