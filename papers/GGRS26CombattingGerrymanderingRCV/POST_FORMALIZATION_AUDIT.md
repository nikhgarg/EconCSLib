# Post-Formalization Audit: GGRS26 Combatting Gerrymandering with Ranked Choice Voting

## Scope

This file records the current formalized state for the in-scope theorem ledger of
*Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis
of Multi-member Districts in the United States*. The source cache is the arXiv
paper, with Operations Research metadata recorded in the README.
The closeout narrative for researchers is `FINAL_VALIDATION_REPORT.md`.

Current status: formalized. Lemma C.1's PAV path, the STV party-isolation
lemma, Droop-quota arithmetic, and Proposition 1 are represented through a
19-row review surface. The final Proposition 1 theorem uses the generated,
total, quota-respecting filled-seat fractional STV source run and reads the STV
party outcome through `partyFilledSeatCount`; the old `helectCount` final-seat
premise is no longer exposed.

## Named Source Inventory

| Source item | Current status | Notes |
|---|---|---|
| PAV/Thiele committee-score vocabulary | formalized | Reuses `EconCSLib.SocialChoice.Voting.Thiele`. |
| Two-party PAV seat-score objective | formalized | `paper_pav_seat_score`. |
| Leftmost PAV min-argmax selector | formalized | `paper_pav_min_argmax`. |
| Lemma C.1 marginal conditions | formalized | `paper_pav_marginal_conditions`. |
| Lemma C.1 PAV interval | formalized | `paper_pav_min_argmax_seat_interval`. |
| Lemma C.1 / Proposition 1 PAV rounding | formalized | `paper_pav_min_argmax_seat_share_rounded`. |
| Proposition 1 generated filled-seat fractional STV route | formalized | The generated source run supplies the trace and terminal active set; total filled-seat accounting and two-party decomposition are proved in Lean, and the party result is read through `partyFilledSeatCount`. |
| Proposition 1 STV solid-coalition party isolation | formalized | `paper_stv_solid_coalition_ballots_party_trace_isolation` proves the no-outside-active-support step from same-party-first ballots. |
| Proposition 1 STV quota-capacity arithmetic | formalized | `paper_stv_quota_floors_fit`. |
| Proposition 1 STV quota-witness bridge | formalized | The quota-witness lower-bound bridge is closed and consumed by the final generated filled-seat endpoint. |
| Proposition 1 STV quota-witness-to-lower-bound bridge | formalized | Reuses `Voting.STV.Quota`. |
| Proposition 1 STV lower-bound-to-rounding bridge | formalized | Reuses `Voting.Proportionality`. |
| Proposition 1 STV/PAV rounded seat shares | formalized | Closed from the generated filled-seat fractional STV source run, total/quota-respecting choice, solid-coalition ballots, source voter/candidate partitions, and the PAV min-argmax theorem. |
| Redistricting optimization, simulations, and empirical sections | out of Lean scope | Data/code boundary, not a theorem-ledger target. |

## Source-Scope Note

The final Proposition 1 row exposes the source choice-rule hypotheses
`choice.Total` and quota-respecting choice for the Droop quota. These are the
algorithmic conventions used by the generated filled-seat STV source model, not
paper-local proof certificates. Redistricting optimization, map generation,
simulations, and empirical claims remain data/code scope outside the theorem
ledger.

## DAG Audit

`DependencyDAG.tex` records the PAV Lemma C.1 path, filled-seat STV source
semantics, and Proposition 1 as formalized. Rebuild and visually inspect
`DependencyDAG.pdf` before a public closeout claim.

## Human Review Surface

The dashboard surface is 19 paper-facing rows. Human dashboard sign-off has not
yet been recorded. Source-record, statement, review-surface, and paper-coverage
sidecars are current for the compact post-closeout `PaperInterface.lean`
surface.

## Library Extraction Review

Reusable infrastructure used or added by this pass:

- `EconCSLib.SocialChoice.Voting.Thiele` for PAV/Thiele scores.
- `EconCSLib.SocialChoice.Voting.STV.Quota` for Droop-quota arithmetic.
- `EconCSLib.SocialChoice.Voting.STV.SolidCoalition` for same-party
  trace-isolation, executable fractional weight folds, solid-coalition
  fold-restriction lemmas, executable trace certificates, terminal active fill
  sets, party filled-seat counters, filled-seat total accounting, two-party
  decomposition, capacity-fill lower-bound lemmas, and source-step/quota-witness
  bridges.
- `EconCSLib.SocialChoice.Voting.Proportionality` for two-party floor/ceiling
  seat-share arithmetic.

No additional paper-specific extraction is currently required; future STV/RCV
papers should reuse the filled-seat total-count and two-party decomposition
theorems for `fractionalSTVFilledSeatRunFocuses`, `terminalFillActive`, and
`partyFilledSeatCount`.

## Commands

Current validation target:

```bash
lake build EconCSLib.SocialChoice.Voting.STV.SolidCoalition GGRS26CombattingGerrymanderingRCV
```

Latest closeout/status audit:

```bash
python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0
```

The closeout audit must be rerun after refreshing stale LLM sidecars for the
current compact interface if the review surface changes again.
