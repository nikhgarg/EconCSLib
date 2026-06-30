# GGRS26 Filled-STV Stopping Point

Date: 2026-06-30

Superseded closeout note: the filled-seat source-model seam described below has
since been closed. Use `START_HERE_NEXT_AGENT.md`,
`FINAL_VALIDATION_REPORT.md`, and `POST_FORMALIZATION_AUDIT.md` for the current
state. The current GGRS target builds and the paper closeout audit passes with
0 errors and 0 warnings.

## Status

GGRS remains partially formalized. The current stopping point is a compiled
library seam for source-faithful filled-seat fractional STV: quota-election
prefixes and terminal active candidates are represented separately, so the
formalization does not pretend that below-quota terminal fills are ordinary
quota-transfer election rounds.

The targeted build passed after the latest edits:

```bash
lake build EconCSLib.SocialChoice.Voting.STV.SolidCoalition GGRS26CombattingGerrymanderingRCV
```

## Files To Read First

1. `papers/GGRS26CombattingGerrymanderingRCV/README.md`
2. `papers/GGRS26CombattingGerrymanderingRCV/PaperInterface.lean`
3. `papers/GGRS26CombattingGerrymanderingRCV/MainTheorems.lean`
4. `EconCSLib/SocialChoice/Voting/STV/SolidCoalition.lean`

## Reusable Library Additions

The new compiled STV library surface is in
`EconCSLib/SocialChoice/Voting/STV/SolidCoalition.lean`.

Useful declarations:

- `fractionalSTVFilledSeatRunFocuses`
- `fractionalSTVFilledSeatRunTrace`
- `fractionalSTVFilledSeatRunTerminalActive`
- `fractionalSTVIndexedExecutableTrace_of_filledSeatRun`
- `fractionalSTVFilledSeatRun_get_noquota_if_eliminate`
- `fractionalSTVIndexedExecutableTrace_of_filledSeatRun_get_noquota_if_eliminate`
- `terminalFillActive`
- `partyFilledSeatCount`
- `floor_votes_div_quota_le_replaySteps_lowerBound_capacityFill`
- `floor_votes_div_quota_le_finalSeats_of_replaySteps_lowerBound_capacityFill`
- `floor_votes_div_quota_le_finalSeats_of_executableTrace_solidCoalition_left_lowerBound_capacityFill`

These give the next agent a real source-shaped API for the paper's terminal
fill semantics. They are not yet wired into the final GGRS Proposition 1 row.

## Active Proof Seam

The current paper-facing GGRS row is still:

```lean
paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax
```

It still consumes:

```lean
helectCount :
  electStepCount
      (fractionalSTVSeatRunTrace choice allVoters ballots
        (STVQuota seats voters : ℝ) seats rounds 0 initialActive
        initialWeight).steps = seats
```

That premise is the remaining source-closure gap. It should not be treated as
an approved external boundary.

The intended replacement route is:

1. Prove a total-seat theorem for `fractionalSTVFilledSeatRunFocuses`:
   quota-election steps plus `terminalFillActive` seats equal `seatLimit`
   under the source capacity/fuel assumptions.
2. Prove the party decomposition theorem:
   `partyFilledSeatCount partyCandidates seats steps terminalActive +
   partyFilledSeatCount otherPartyCandidates seats steps terminalActive =
   seats` under the existing disjoint/covered candidate assumptions.
3. Rewire the Proposition 1 GGRS theorem to use `partyFilledSeatCount` and the
   capacity-fill lower-bound lemmas, instead of `helectCount` on
   `fractionalSTVSeatRunTrace`.
4. Only after that, refresh the paper-local LLM/source-record sidecars and run
   the closeout audit.

## Do Not Redo

- Do not reintroduce a replay/process/certificate object as a paper-facing
  assumption.
- Do not count terminal below-quota fills as quota-election rounds.
- Do not move on to the DGJ papers until the GGRS source-primitive row no
  longer exposes the filled-seat/elected-count premise.
- Do not run the repo-wide audit for this checkpoint; the current request only
  needs targeted GGRS status and validation.

## Minimal Validation

Use these checks for the next proof iteration:

```bash
lake build EconCSLib.SocialChoice.Voting.STV.SolidCoalition GGRS26CombattingGerrymanderingRCV
rg -n "helectCount|sorry|admit|axiom|constant|opaque" papers/GGRS26CombattingGerrymanderingRCV EconCSLib/SocialChoice/Voting/STV/SolidCoalition.lean
python3 scripts/private_paper_checkpoint.py GGRS26CombattingGerrymanderingRCV --include-path EconCSLib/SocialChoice/Voting/STV.lean --include-path EconCSLib/SocialChoice/Voting/STV/SolidCoalition.lean --include-path skills/econcs-formalizer/references/proof-markets-social-choice.md --include-path docs/PRIVATE_DEVELOPMENT_WORKFLOW.md --include-path scripts/private_paper_checkpoint.py
```

The `helectCount` grep should keep finding the current source gap until the
replacement theorem is proved.
