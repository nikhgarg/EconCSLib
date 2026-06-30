# Start Here: GGRS26

Current status: formalized, 19 paper-facing review rows. The in-scope theorem
ledger closed on 2026-06-30 and the paper closeout audit passes with no
warnings.

Begin by running:

```bash
lake build EconCSLib.SocialChoice.Voting.STV.SolidCoalition GGRS26CombattingGerrymanderingRCV
```

Read in this order:

1. `FINAL_VALIDATION_REPORT.md`
2. `POST_FORMALIZATION_AUDIT.md`
3. `README.md`
4. `PaperInterface.lean`
5. `MainTheorems.lean`
6. `EconCSLib/SocialChoice/Voting/STV/SolidCoalition.lean`

The old filled-seat source-model seam for Proposition 1's STV side is closed.
Do not reopen the old process/replay surface as the paper-facing boundary, and
do not count terminal below-quota fills as ordinary quota-election transfer
rounds.

The current paper-facing generated-run endpoint is:

`paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax`.

It no longer exposes the old `helectCount` source gap. The final route derives
filled-seat accounting from source primitives and reads the party outcome
through `terminalFillActive` / `partyFilledSeatCount`.

Latest closeout evidence:

- `lake build GGRS26CombattingGerrymanderingRCV`: passed.
- `python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0`: passed with 0 errors and 0 warnings.

Shared-library note: `EconCSLib.SocialChoice.Voting.STV.SolidCoalition` now has
the generated filled-seat runner, terminal active fill set, party filled-seat
counter, filled-seat total-count/decomposition lemmas, and capacity-fill
lower-bound lemmas used by the final proof.
