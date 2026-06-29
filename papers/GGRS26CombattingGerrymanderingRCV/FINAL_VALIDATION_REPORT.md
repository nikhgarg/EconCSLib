# Final Validation Report: Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States

## 1. Human Verdict
The 19-row in-scope theorem ledger is Lean-closed. The PAV side is formalized
from the paper's min-argmax selector through the interval and rounded-seat
conclusions, and the STV side is formalized for the source-facing
solid-coalition quota-process outcome predicate. No paper-local assumption
declarations remain. Empirical redistricting artifacts remain data/code
boundaries, not theorem-ledger targets. No human dashboard sign-off has been
recorded.

## 2. Closeout Status
- Completion status: formalized for the in-scope theorem ledger
- One-sentence recap: PAV/Thiele library tooling and the GGRS PAV theorem path
  build, and the STV quota-process theorem path now builds without a paper-local
  assumption declaration.

## 3. Source and Scope
- Paper: *Combatting Gerrymandering with Ranked Choice Voting: an Experimental
  Analysis of Multi-member Districts in the United States*
- Source version: arXiv:2107.07083; Operations Research 2026, DOI
  10.1287/opre.2024.1167
- Lean folder: `papers/GGRS26CombattingGerrymanderingRCV`
- Human-facing theorem file: `papers/GGRS26CombattingGerrymanderingRCV/PaperInterface.lean`
- Paper assumption file: `papers/GGRS26CombattingGerrymanderingRCV/Assumptions.lean`
- DAG artifacts: `papers/GGRS26CombattingGerrymanderingRCV/DependencyDAG.tex`, `papers/GGRS26CombattingGerrymanderingRCV/DependencyDAG.pdf`
- Lean footprint: `PaperInterface.lean` has 342 lines.

## 4. Researcher Summary of Checked Results
- The paper's PAV/Thiele committee-score vocabulary is represented through
  reusable `EconCSLib.SocialChoice.Voting.Thiele` definitions.
- The two-party PAV seat-count objective and leftmost argmax selector are
  exposed in `paper_pav_seat_score` and `paper_pav_min_argmax`.
- Lemma C.1's PAV interval consequence is formalized in
  `paper_pav_min_argmax_seat_interval`.
- The interval-to-floor/ceiling rounding consequence is formalized in
  `paper_pav_min_argmax_seat_share_rounded`.
- Proposition 1 is a Lean-closed theorem from the formal appendix STV
  solid-coalition outcome predicate and the formalized PAV min-argmax theorem.
  The process-to-quota-witness and quota-witness-to-lower-bound steps use
  reusable `Voting.STV.SolidCoalition` certificates and
  `Voting.STV.Quota` arithmetic, and the lower-bound-to-floor/ceiling step uses
  reusable `Voting.Proportionality` arithmetic.

## 5. Remaining Boundaries and Gaps
- The full fractional ballot-level STV trace/replay semantics are still not
  modeled. The paper-facing theorem uses the source-shaped solid-coalition
  quota-process outcome predicate rather than a ballot simulator.
- Redistricting optimization, map generation, simulations, and empirical claims
  remain explicit data/code boundaries outside the in-scope theorem ledger.
- Statement, source-coverage, and assumption-provenance sidecars have been
  refreshed for the 19-row theoretical review surface. Human dashboard review
  remains unrecorded.

## 6. Additional Assumptions Beyond Paper
- None.

## 7. Proof-Strategy Deviations
- None

## 8. Proof Tricks Worth Reusing
- Two-party PAV argmax proofs can be routed through reusable harmonic
  marginal-weight comparisons in `EconCSLib.SocialChoice.Voting.Thiele`.

## 9. Paper Issues or Caveats
- No source contradiction found in this pass. The STV half of Proposition 1 is
  not yet derived from primitive STV trace semantics.

## 10. Detailed Formalization Evidence
- `lake build GGRS26CombattingGerrymanderingRCV` completed successfully after
  the PAV theorem and assumption-boundary updates.
- `latexmk -pdf DependencyDAG.tex` completed successfully, and the rendered DAG
  was visually inspected after a spacing correction.

## 11. Paper Assumption Provenance
Every paper-facing theorem premise that is not derived in Lean should appear as
a named assumption declaration in `Assumptions.lean`, be listed in `status.json`
`review_surface.assumption_names`, and be checked in `assumption_match_llm.json`
as a true paper/source model assumption.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | None | No paper-local assumption declaration remains | Not run | `paper_stv_solid_coalition_process_bounds` is now an ordinary source-facing predicate in `PaperInterface.lean`. |

## 12. Library Lift Pass
- Reusable library extraction candidates: None
- Library certificate/source-boundary audit: passed as part of the current
  paper-closeout repository audit. The reused STV quota-process APIs are
  constructive Lean predicates/certificates; a full ballot-level replay audit
  remains outside this theorem-ledger scope.
- Paper-local hidden-premise audit: passed in
  `python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0`
  with 0 errors and 0 warnings.
- Recursive provenance closeout report: no unresolved recursive provenance
  finding for the in-scope theorem ledger in the current paper-closeout audit.

## 13. DAG Audit
- Rendered artifact: `DependencyDAG.pdf` rebuilt with `latexmk`.
- Topology: PAV Lemma C.1 path and the Proposition 1 STV/PAV rounding path are
  formalized for the source-facing solid-coalition STV outcome predicate;
  redistricting/simulation remains a data/code boundary.
- Layout: visually inspected after PNG conversion; no node overlap after the
  final spacing pass.

## 14. Validation Checks
- `lake build GGRS26CombattingGerrymanderingRCV.PaperInterface`: passed after
  removing the paper-local assumption alias.
- `lake build GGRS26CombattingGerrymanderingRCV`: passed after the shared quota
  arithmetic and interface/status updates.
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --precheck`:
  passed structurally with 19 unreviewed human-review rows and no
  stale/mismatch rows.
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --statement-precheck`:
  current, with 19 Lean-to-TeX drafts and 19 statement-judge rows.
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --paper-coverage-precheck`:
  current, with 19/19 source statements covered directly.
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --assumption-precheck`:
  current, with zero assumption declarations and no missing/stale/flagged
  items.
- `python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0`:
  passed with 0 errors and 0 warnings.
- `latexmk -pdf DependencyDAG.tex`: passed after the DAG node-status update.
- Rendered `DependencyDAG.pdf` was converted to PNG and visually inspected; no
  node overlap or stale partial STV/Proposition node styling remained.
- `latexmk -pdf DependencyDAG.tex`: passed.
- Recursive all-repo provenance audit: not run in this active-proof pass.
- Required closeout checks include targeted Lean build, statement precheck,
  assumption/hidden-premise precheck, targeted repository audit, DAG/report
  closeout audit, and library premise audit when reusable certificate APIs are
  used or when preparing a public PR. The repository audit must also be clean of
  axiom-like declarations, stale final-report placeholders, missing
  `DependencyDAG.pdf`, and unrecorded DAG visual-inspection evidence.
- Machine-required closeout evidence may include the exact targeted repository
  audit command here, but keep commands out of the executive verdict and proof
  narrative.

## 15. Paper Definitions Checked
- `paper_pav_score`
- `paper_pav_seat_score`
- `paper_pav_min_argmax`
- `paper_pav_marginal_conditions`
- `paper_pav_seat_interval`
- `paper_seat_share_rounded`
- `paper_stv_solid_coalition_process_bounds`
- `paper_stv_solid_coalition_quota_witness_bounds`
- `paper_stv_solid_coalition_lower_bounds`
- `paper_stv_seat_share_bounds`

## 16. Named Theorem Statements Checked
### Lemma C.1 PAV Interval

**Lean interface statement.**
- `paper_pav_min_argmax_seat_interval`: the paper's leftmost maximizing PAV
  seat count satisfies `y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.

**Status.** formalized.

### Proposition 1 Reduction

**Lean interface statement.**
- `paper_stv_solid_coalition_process_bounds_quota_witness_bounds`: the named
  STV terminal process boundary implies the quota-witness boundary.
- `paper_stv_quota_floors_fit`: the two parties' canonical Droop-quota floors
  fit into the district's seat count.
- `paper_stv_solid_coalition_quota_witness_bounds_lower_bounds`: the named STV
  quota-witness boundary implies the proportional lower-bound boundary.
- `paper_stv_solid_coalition_lower_bounds_seat_share_bounds`: the proportional
  lower-bound boundary implies the STV floor/ceiling seat-share bound.
- `paper_proposition1_from_stv_bounds_and_pav_min_argmax`: from the named STV
  solid-coalition terminal process boundary and the paper's PAV min-argmax
  selector, both STV and PAV seat counts are rounded vote shares.

**Status.** formalized for the source-facing solid-coalition STV outcome
predicate.

## 17. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Generate it from the
validator ledger rather than from memory.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| PAV score vocabulary | `paper_pav_score` | Lean build; statement sidecar; source-coverage sidecar | Covered directly by source-grounded review metadata. |
| PAV seat objective | `paper_pav_seat_score` | Lean build; statement sidecar; source-coverage sidecar | Covered directly by source-grounded review metadata. |
| PAV min-argmax selector | `paper_pav_min_argmax` | Lean build; statement sidecar; source-coverage sidecar | Covered directly by source-grounded review metadata. |
| Lemma C.1 interval | `paper_pav_min_argmax_seat_interval` | Lean build; statement sidecar; source-coverage sidecar | Covered directly by source-grounded review metadata. |
| PAV rounded-seat consequence | `paper_pav_min_argmax_seat_share_rounded` | Lean build; statement sidecar; source-coverage sidecar | Covered directly by source-grounded review metadata. |
| STV terminal process boundary | `paper_stv_solid_coalition_process_bounds` | Lean build; statement sidecar; source-coverage sidecar | Source-facing formal STV outcome predicate; no paper-local assumption declaration remains. |
| STV quota-capacity step | `paper_stv_quota_floors_fit` | Lean build; statement sidecar; source-coverage sidecar | Closed reusable Droop-quota arithmetic. |
| STV process-to-quota-witness bridge | `paper_stv_solid_coalition_process_bounds_quota_witness_bounds` | Lean build; statement sidecar; source-coverage sidecar | Closed from the named terminal process boundary. |
| STV quota-witness bridge | `paper_stv_solid_coalition_quota_witness_bounds_lower_bounds` | Lean build; statement sidecar; source-coverage sidecar | Closed from the quota witness derived from the process boundary. |
| STV lower-bound bridge | `paper_stv_solid_coalition_lower_bounds_seat_share_bounds` | Lean build; statement sidecar; source-coverage sidecar | Closed after the process-to-quota-witness bridge. |
| Proposition 1 reduction | `paper_proposition1_from_stv_bounds_and_pav_min_argmax` | Lean build; statement sidecar; source-coverage sidecar | Closed for the source-facing solid-coalition STV outcome predicate. |

Human dashboard reviews and model/agent statement checks may both appear here.
This table is provenance for the statement targets; it does not change the
human-only `human_review.reviewed_rows` counter.
