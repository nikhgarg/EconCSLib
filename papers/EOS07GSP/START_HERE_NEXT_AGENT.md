# EOS07GSP Startup Handoff

Date: 2026-06-03

This is the first file to read after the pause. It is intentionally shorter
than the older handoff and points to exact files/declarations for the next
proof pass.

For the current proof strategy, read the "Fastest paper-DAG screening path"
section below before opening the large theorem files. The Theorem 8 finite
endpoint is useful, but the paper-level DAG still has upstream conditional
nodes at Lemmas 5--6 and Theorem 7.

## Current Validation Boundary

The latest Lean validation after the finite exact-record direct-PBE
price-sorted endpoint was:

```bash
lake build EOS07GSP.ProofInterface EOS07GSP.PostPaperAudit EOS07GSP.PaperInterface EOS07GSP
```

That command passed after the latest Theorem 8 source-boundary work. Rerun it
before any further Lean commit.

## Shared Worktree Rules

- Do not use `git reset` in this repository. Other agents may have staged or
  unstaged work.
- Do not run broad `git add .`.
- Before editing, check only the owned paths:

```bash
git status --short --branch -- \
  EconCSLib/MechanismDesign/Auctions/MainTheorems.lean \
  papers/EOS07GSP \
  skills/econcs-formalizer
```

- If committing EOS work, use `git commit --only` with explicit path names.

## Fastest Paper-DAG Screening Path

The DAG path is:

```text
Definition 4 -> Lemma 5 -> Lemma 6 -> Theorem 7 -> Theorem 8
```

The finite exact-record Theorem 8 endpoint does not discharge Lemma 5, Lemma 6,
or Theorem 7. It is a closed finite/direct-PBE route inside Theorem 8's dynamic
machinery. For the fastest paper-level progress and the most rows moving from
conditional to formalized, do this before returning to the full Theorem 8
source-game proof:

1. Close Lemma 5. Target the appendix bridge from adjacent/local envy-free
   equilibrium facts to the global formal no-rematch/stable-assignment
   predicate. The current Lean theorem already proves stability from the
   stronger all-assigned-slot `SlotEnvyFree` predicate; the missing work is the
   source bridge from the paper's adjacent LEF/equilibrium/no-tie/order
   assumptions to that predicate.
2. Close Lemma 6. Target the paper's stable-assignment-to-GSP/LEF construction
   under `N > K`: Shapley-Shubik stable-assignment characterization, the bid
   construction, and the static-equilibrium converse. The current Lean theorem
   only proves the outcome-level implication because `StableAssignment` already
   contains no-rematch inequalities.
3. Close Theorem 7. Reuse the existing `B*`, VCG-tail, ordered-values
   envy-free/stability, no-positive-transfer, and revenue-minimality algebra.
   The remaining paper-level cleanup is to remove or derive the explicit
   comparison-outcome no-positive-transfers/no-subsidy premise and route the
   result through the now-closed Lemmas 5--6.
4. Return to full Theorem 8 only after the upstream static path is green, or if
   the user explicitly asks for more Theorem 8 source-game work.

This is the quickest path to making more source rows screen as formalized. More
finite Theorem 8 schedule wrappers should wait unless a reviewer asks for a
different finite presentation.

## What Is Actually Open

The paper is not finished. After the upstream Lemma 5/Lemma 6/Theorem 7 path,
the remaining open Theorem 8 work is not payment algebra, finite schedule
plumbing, or another display wrapper. The remaining hard seam is the fully
concrete generalized-English source proof:

1. concrete belief consistency for the real source game;
2. the game-level source sequential-rationality iff/local-deviation theorem for
   reachable and off-path histories;
3. source-history generation strong enough to produce exact finite `B*`
   terminal records without assuming a schedule, no-overshoot history, or
   clock-disciplined history as input.

The formal counterexample
`paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_record`
shows that ordinary `StrategyHistory` is too weak: a rank can drop after its
finite `B*` threshold and therefore record the wrong terminal price.

The finite exact-record direct-PBE version is closed. Use
`theorem8_price_sorted_finite_schedule_pbe_displayed_ordered_conclusion` or
`theorem8_price_sorted_finite_schedule_belief_pbe_displayed_ordered_conclusion`
for the canonical finite displayed schedule; these build the price-sorted
`Fin n` schedule internally and retain only the threshold-event timing premise
for the PBE-generated history.

## What To Reuse

Use these as the strongest public entry points before adding new code:

- `theorem8_no_overshoot_strategy_history_to_exact_drop_history`
- `theorem8RealizedNewDropoutNoOvershootStatement`
- `theorem8_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot`
- `theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot`
- `theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot_statement`
- `theorem8_no_overshoot_terminal_certificate_of_strategy_history`
- `theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout`
- `theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout_statement`
- `theorem8_strategy_history_realized_new_dropout_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_strategy_history_realized_new_dropout_statement_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_clock_disciplined_strategy_history_to_exact_drop_history`
- `theorem8_clock_disciplined_strategy_history_final_record_eq_threshold`
- `theorem8_cold_start_clock_disciplined_strategy_history_final_record_eq_threshold`
- `theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion`
- `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_strict_ordered_fin_schedule_belief_source_extensive_displayed_rank_formulas_of_threshold_sorted`
- `theorem8_complete_finite_schedule_pbe_displayed_ordered_conclusion`
- `theorem8_complete_finite_schedule_belief_pbe_displayed_ordered_conclusion`
- `theorem8_price_sorted_finite_schedule_pbe_displayed_ordered_conclusion`
- `theorem8_price_sorted_finite_schedule_belief_pbe_displayed_ordered_conclusion`
- `theorem8_ex_post_local_deviation_exact_history_source_full_conclusion_terminal_record_outcome_eq_bstar`

Search for them with:

```bash
rg -n "theorem8_no_overshoot_strategy_history_to_exact_drop_history|theorem8_clock_disciplined_strategy_history_to_exact_drop_history|price_sorted_finite_schedule_pbe_displayed_ordered|belief_source_extensive_trace_all_terminal|ex_post_local_deviation_exact_history_source_full_conclusion" papers/EOS07GSP EconCSLib/MechanismDesign/Auctions
```

## Next Proof Target

If continuing the full Theorem 8 source proof, do this in this order:

1. Pick the source-history invariant to prove. The most promising route is a
   cold-start source transition theorem that produces
   `PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory`, or a
   no-overshoot named-strategy history, from the real generalized-English
   source semantics.
2. Prove the invariant for one transition first. The useful statement is not
   another final conclusion; it should supply the no-overshoot premise consumed
   by `theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot`
   and its one-step record form
   `theorem8_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot`,
   or else prove the named source-timing premise
   `theorem8RealizedNewDropoutNoOvershootStatement`.
3. Lift the one-transition invariant to histories.
4. Feed the resulting history into the existing cold-start clock-disciplined or
   no-overshoot source-extensive endpoints.
5. Only after that, update `PaperInterface.lean` and `PostPaperAudit.lean` with
   a small paper-facing theorem.

If the real source semantics permits overshoot, do not hide that with a wrapper.
Either formalize the missing paper assumption, switch to a finite-bidder source
model whose transition rule prevents overshoot, or record the theorem as
conditional on no-overshoot/clock-discipline.

## What Not To Spend Time On

- Do not add more finite-schedule endpoints unless a reviewer asks for a
  different finite presentation or the endpoint removes a source-history
  premise from the full theorem. The canonical finite direct-PBE endpoint is
  already exposed.
- Do not try to derive an all-ranks-inactive conclusion from a finite schedule
  in the current `ℕ`-rank cold-start model. Lean already proves
  `theorem8_cold_start_clock_sorted_finite_schedule_leaves_active_unscheduled_rank`.
- Do not replace the remaining source proof with a reduced-form dynamic-game
  certificate. Reduced-form endpoints validate the certificate plumbing but do
  not finish the paper's generalized-English extensive-form theorem.

## Files To Read

Read in this order:

1. `README.md`, especially the handoff and Theorem 8 source-boundary sections.
2. `THEOREM8_SOURCE_PROOF_PLAN.md`, especially `Remaining source gap` and
   `Source-PBE obligations after the schedule layer`.
3. `POST_PAPER_AUDIT_REPORT.md`, especially the Theorem 8 history-semantics,
   source-extensive, and belief-explicit audit bullets.
4. `FINAL_VALIDATION_REPORT.md` for the paper-facing source inventory and
   caveats.
5. `HANDOFF_2026-05-06.md` only if you need the older detailed declaration
   ledger.

## Validation Commands

After any Lean edit:

```bash
lake build EOS07GSP.ProofInterface EOS07GSP.PostPaperAudit EOS07GSP.PaperInterface EOS07GSP
```

After documentation-only edits, at least run:

```bash
git diff --check -- papers/EOS07GSP skills/econcs-formalizer README.md
```
