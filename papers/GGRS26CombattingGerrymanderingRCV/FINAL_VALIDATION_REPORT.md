# Final Validation Report: Combatting Gerrymandering with Ranked Choice Voting

## 1. Human Verdict

The in-scope theorem ledger is formalized. Lemma C.1, the PAV rounding path,
solid-coalition STV isolation, Droop-quota arithmetic, and Proposition 1 are
closed in Lean through the 19 paper-facing rows in `PaperInterface.lean`.

No human dashboard sign-off has been recorded.

## 2. Closeout Status

- Completion status: formalized
- Paper-facing rows: 19
- `PaperInterface.lean` footprint: 403 lines
- Main Lean target: `lake build GGRS26CombattingGerrymanderingRCV`

## 3. Source and Scope

The formalized source version is the arXiv paper with Operations Research 2026
metadata recorded in `README.md`. The theorem ledger covers the theoretical
Lemma C.1 and Proposition 1 path.

Redistricting optimization, map generation, simulations, and empirical claims
remain data/code scope outside this theorem ledger.

## 4. Researcher Summary of Checked Results

- PAV/Thiele committee-score vocabulary and two-party PAV seat-score wrappers.
- Lemma C.1 PAV interval and interval-to-rounded-seat-share consequences.
- Solid-coalition ballot party-isolation bridge for STV traces.
- Droop-quota and proportionality arithmetic used by Proposition 1.
- Proposition 1 from the generated filled-seat fractional STV source run and
  the PAV min-argmax theorem to rounded STV/PAV seat shares.

## 5. Remaining Boundaries and Gaps

None for the theorem ledger. The remaining non-Lean scope is empirical/data/code
work: district generation, simulations, and redistricting optimization.

## 6. Additional Assumptions Beyond Paper

No paper-local assumptions are declared in `Assumptions.lean`. The final
Proposition 1 theorem exposes source model hypotheses directly, including
`choice.Total` and quota-respecting choice for the Droop quota.

## 7. Proof-Strategy Deviations

The final STV statement reads the party result through `partyFilledSeatCount`
on the generated filled-seat run. This replaces the earlier proof-route
`helectCount` premise with Lean-checked filled-seat accounting.

## 8. Proof Tricks Worth Reusing

- Model terminal fill candidates separately from quota-election rounds.
- Use `partyFilledSeatCount` to count elected candidates plus terminal fill
  candidates in a source-level filled-seat STV run.
- Keep `PaperInterface.lean` to the review surface; leave historical proof
  route aliases in implementation files.

## 9. Paper Issues or Caveats

No source-quality caveat is recorded for the formalized theoretical theorem
ledger.

## 10. Detailed Formalization Evidence

- `PaperInterface.lean` exposes 19 source-facing definitions and theorem rows.
- `MainTheorems.lean` contains the implementation route from PAV/Thiele
  arithmetic, solid-coalition STV isolation, filled-seat STV accounting, and
  Droop-quota bounds to Proposition 1.
- `EconCSLib.SocialChoice.Voting.STV.SolidCoalition` now contains reusable
  filled-seat total-count and two-party decomposition lemmas.

## 11. Review Surface Audit

The review dashboard sidecars are current for the compact 19-row surface:
statement translation, statement match, paper coverage, source-to-Lean, and
assumption/source-record provenance prechecks all report no missing, stale, or
flagged items.

## 12. Validation Commands

- `lake build GGRS26CombattingGerrymanderingRCV`
- `lake build EconCSLib.SocialChoice.Voting.STV.SolidCoalition`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --statement-precheck`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --paper-coverage-precheck`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --source-to-lean-precheck`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --assumption-precheck`
- `latexmk -pdf DependencyDAG.tex`
- `python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0`

## 13. DAG Audit

`DependencyDAG.tex` uses the shared DAG preamble and records the PAV Lemma C.1
path, filled-seat STV source semantics, STV rounding, and Proposition 1 as
formalized. `DependencyDAG.pdf` was regenerated after the closeout DAG update.
