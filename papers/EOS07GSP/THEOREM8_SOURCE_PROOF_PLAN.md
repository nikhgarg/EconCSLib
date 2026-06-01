# EOS07GSP Theorem 8 source proof plan

This is a live scratch plan for completing the source-level generalized-English
auction proof. It is intentionally less formal than Lean, but every stable seam
should become a named Lean declaration and an audit wrapper in
`PostPaperAudit.lean`.

After the 2026-05-16 pause, start from `START_HERE_NEXT_AGENT.md`. That file
summarizes the current validation boundary, the shared-worktree rules, and the
specific source-history/PBE seam to attack before rereading this longer plan.

## Current verified boundary

- The scalar and ranked dropout-price algebra is formalized.
- The named finite `B*` ranked-threshold strategy is formalized.
- Local optimality, strict behavior regions, no-early-drop, and drop-by-value
  consequences are formalized.
- The abstract dynamic/PBE certificate layer proves unique PBE and VCG
  slot/payment conclusions once belief consistency, sequential rationality, and
  behavioral PBE characterization are supplied.
- The terminal dropout-record outcome algebra is closed:
  exact terminal records imply the constructed ranked `B*` outcome.
- Exact-drop histories now give:
  rank-local terminal payment/VCG-tail conclusions,
  finite completed-rank conclusions,
  all-ranks ordered terminal-record outcome conclusions,
  finite exact-history terminal-dynamic certificates,
  finite exact-history source-completion unique-PBE endpoints,
  a single exact-drop constructor, and
  exact-history transitivity plus append-single and list-schedule constructors
  for composing checked segments.
- Finite exact schedules now feed terminal-dynamic and source-completion
  certificates directly, so the strongest finite endpoint can take a concrete
  ordered schedule list rather than an opaque exact-history witness.
- A sorted-threshold/no-duplicate constructor now builds the finite exact-drop
  schedule automatically from an initially active rank list, a clock-sorted
  threshold proof, and no duplicates.
- The paper interface now explicitly records that a finite cold-start schedule
  over the current `ℕ`-rank state leaves an unscheduled rank active:
  `theorem8_cold_start_clock_sorted_finite_schedule_leaves_active_unscheduled_rank`.
  This rules out using finite schedules alone to discharge all-ranks-inactive
  all-terminal endpoints in the current model.
- The core source-completion layer separates the independent source PBE
  obligations from derived outcome facts: once named-strategy belief
  consistency, named-strategy sequential rationality, and behavioral PBE
  threshold characterization are proved, Lean derives arbitrary-PBE equality to
  the VCG slot/payment outcome from behavioral uniqueness plus the constructed
  `B*` outcome agreement.
- The finite exact-history and sorted finite-schedule endpoints now have core
  source-completion versions, so the strongest finite human-facing endpoint can
  take only the three core source-PBE obligations plus the exact schedule.
- A one-stop constructor now builds the finite-schedule core
  source-completion certificate directly from the terminal-dynamic certificate,
  final-state equality, clock-sorted no-duplicate schedule, and completed-rank
  inclusion facts.
- Exact-drop schedules now bridge directly to named finite-`B*`
  strategy-consistent histories, including a clock-sorted/no-duplicate wrapper.
  This is the reachability object needed by any future sequential-rationality
  proof over concrete histories.
- Exact-drop schedules now also build the terminal-history behavior certificate
  once unscheduled ranks are checked to have finite `B*` thresholds above the
  final clock. This replaces a broad manual `StrategyTerminal` obligation with
  a rank-local threshold check; the same constructor is available directly from
  clock-sorted/no-duplicate schedule data.
- Final-clock helper lemmas for empty, nonempty, singleton, and pair schedules
  make these unscheduled-threshold checks concrete without unfolding the
  deterministic final-state recursion.
- The terminal-history constructor now lifts to an integrated strict ordered
  terminal-dynamic certificate from a strict ordered dynamic-game certificate
  plus the same sorted schedule and unscheduled-threshold facts.
- These constructors now compose all the way to the finite-schedule core
  source-completion certificate from a strict ordered dynamic-game certificate,
  sorted/no-duplicate schedule data, unscheduled-threshold facts, and
  completed-rank inclusion.
- The same data now has a direct unique-PBE terminal-record endpoint:
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_core_source_completion_exists_unique_pbe_of_dynamic_clock_sorted_nodup_unscheduled_threshold_gt`.
- The same sorted schedule data also has a direct full ordered-outcome PBE
  endpoint:
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_dynamic_clock_sorted_nodup_unscheduled_threshold_gt`.
- The terminal-record local-deviation dynamic game now has exact/no-overshoot
  completed-rank slot/payment and utility endpoints. For finite paper checks,
  the exact and no-overshoot `...completed_threshold_le` forms derive
  completed-rank inactivity from the terminal clock reaching each completed
  rank's finite `B*` threshold, so the audit does not need an all-ranks
  terminal-inactivity premise.
- A cold-start threshold-sorted schedule endpoint now feeds that
  terminal-record game directly: a displayed nonempty no-duplicate schedule,
  adjacent-threshold sortedness, and the last-threshold terminality check imply
  completed-rank slot/payment and utility equality for any PBE on each
  scheduled rank. Singleton and pair specializations expose the common small
  cases directly, so a one-rank check only needs the unscheduled-threshold
  comparison and a two-rank check only needs adjacent threshold order,
  distinctness, and unscheduled-threshold comparisons.
- The terminal-record game also has finite completed-rank unique-PBE packages
  for exact, no-overshoot, threshold-reached, and cold-start threshold-sorted
  routes, including singleton and pair specializations. Use these when checking
  the paper's equilibrium claim itself, not just a consequence for an
  already-given PBE.
- Exact and no-overshoot completed-rank paper-conclusion endpoints now turn
  terminal-record game PBE facts into the displayed rank assignment, finite
  `B*` threshold payment, VCG-tail accounting, and `[0, value]` payment
  interval under ordered assumptions. Matching unique-PBE wrappers bundle those
  displayed formulas with the equilibrium uniqueness claim.
- The concrete no-overshoot source-history route no longer needs the ex-post
  source certificate. Use the local-deviation core endpoints with prefix
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_core_source_completion_..._of_histories_no_overshoot`
  after proving generated histories and no-overshoot timing. From the
  reachable/off-path certificate, use the source-shaped slot/payment, outcome,
  and utility wrappers; the outcome endpoint is
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_all_pbe_outcome_eq_vcg_of_histories_no_overshoot`.
  The full source-completion certificate is then available directly as
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_completion_certificate_of_source_sequential_rationality_and_histories_no_overshoot`.
  The corresponding one-stop unique-PBE/full-conclusion theorem is
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_histories_no_overshoot_exists_unique_pbe_with_full_conclusion`.
  Prefer
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion`
  when the source history is already packaged as a no-overshoot
  terminal-dynamic certificate; it uses the annotated finite history instead of
  a global no-overshoot predicate for every possible state.
  For finite displayed rank sets, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion`;
  it only asks for terminal inactivity on the completed finite rank set.
- The cold-start threshold-sorted terminal-record game route has matching
  displayed-formula and unique-PBE displayed-formula wrappers against the named
  exact-schedule local model. Direct singleton and pair forms cover the small
  displayed schedule cases without manual list instantiation.
- The paper proof's Step 1/Step 2 strict payoff comparisons around the
  indifference price `q` are now named as source-proof wrappers:
  `paper_theorem8_source_step1_dropping_after_q_strictly_better`,
  `paper_theorem8_source_step2_waiting_before_q_strictly_better`, and
  `paper_theorem8_source_q_strict_mono_value`.
- The local payoff objects are now first-class: continuing and dropping are
  named by `paper_theorem8_bstar_ranked_threshold_continue_payoff` and
  `paper_theorem8_bstar_ranked_threshold_drop_payoff`, and
  `paper_theorem8_bstar_ranked_threshold_named_strategy_one_step_best_response`
  proves that the named finite `B*` strategy chooses a weakly optimal one-step
  action at every state/rank under the local-optimality certificate.
- The off-threshold strict version
  `paper_theorem8_bstar_ranked_threshold_named_strategy_off_threshold_strict_best_response`
  now packages the paper's Step 1/Step 2 strict preference directions together
  with the named strategy's actual drop/not-drop action.
- Strict and strict-ordered wrappers expose the same one-step and off-threshold
  best-response facts directly from the source-facing strict ordered model, so
  future Theorem 8 work should cite those wrappers rather than manually
  forgetting strict ordered assumptions to weak local assumptions.
- Behavioral uniqueness now has a local route:
  `paper_theorem8_bstar_ranked_threshold_strategy_iff_of_one_step_best_response_and_drop_at_threshold`
  and
  `paper_theorem8_bstar_ranked_threshold_strategy_eq_of_one_step_best_response_and_drop_at_threshold`
  prove that one-step best response plus the paper's at-threshold drop
  tie-breaking convention forces the finite `B*` cutoff rule and extensional
  equality to the named strategy.
- The strict off-threshold part is available separately as
  `paper_theorem8_bstar_ranked_threshold_one_step_best_response_off_threshold_behavior`:
  one-step best response alone forces dropping strictly after the threshold and
  not dropping strictly before it; tie-breaking is only needed at equality.
- If the source proof gives off-threshold behavior directly, use
  `paper_theorem8_bstar_ranked_threshold_strategy_iff_of_off_threshold_behavior_and_drop_at_threshold`
  or
  `paper_theorem8_bstar_ranked_threshold_strategy_eq_of_off_threshold_behavior_and_drop_at_threshold`
  to combine it with at-threshold tie-breaking into the cutoff rule or
  strategy equality, without mentioning payoff optimality.
- The named strategy itself now exposes the tie-breaking fact via
  `paper_theorem8_bstar_ranked_threshold_named_strategy_drop_at_threshold`,
  with strict and strict-ordered wrappers.
- The dynamic sequential-rationality seam now has a narrower certificate,
  `PaperTheorem8BStarRankedThresholdOneStepBestResponseDynamicGameExtensionalOutcomeCertificate`:
  future source work can prove that the audited one-step best-response
  predicate implies the game's sequential-rationality predicate, and Lean
  converts that into the existing local-optimality dynamic-game certificate via
  `paper_theorem8_bstar_ranked_threshold_local_optimality_extensional_outcome_certificate_of_one_step_best_response`.
- The one-step dynamic certificate now has direct named-strategy PBE,
  unique-PBE, generic unique-PBE/VCG, arbitrary-PBE paper conclusion, and
  named-strategy paper-conclusion endpoints, so reviewers can start from that
  narrower seam without manually routing through the local-optimality dynamic
  certificate.
- The behavioral dynamic certificate has also been split:
  `PaperTheorem8BStarRankedThresholdOneStepTieBreakDynamicGameExtensionalOutcomeCertificate`
  replaces the full PBE cutoff characterization field by two local fields:
  every PBE strategy is a one-step best response and every PBE strategy drops
  at exact finite `B*` threshold indifference. Lean derives the cutoff iff,
  unique PBE, and named-strategy paper conclusion from these.
- The source-sequential-rationality split pushes those two PBE behavioral
  fields below the PBE predicate:
  `PaperTheorem8BStarRankedThresholdSequentialRationalityDynamicGameExtensionalOutcomeCertificate`
  and
  `PaperTheorem8BStarRankedThresholdStrictOrderedSequentialRationalityCoreSourceCompletionCertificate`
  ask for one-step best response and threshold tie-breaking as consequences of
  `isSequentiallyRational`; Lean unpacks the PBE witness to derive the
  one-step/tie-break dynamic and core source-completion certificates.
- The local-deviation split is the sharper target:
  `PaperTheorem8BStarRankedThresholdLocalDeviationDynamicGameExtensionalOutcomeCertificate`
  and
  `PaperTheorem8BStarRankedThresholdStrictOrderedLocalDeviationCoreSourceCompletionCertificate`
  require an iff between game-level sequential rationality and the audited
  local one-step best-response plus threshold tie-breaking predicates. This
  derives the sequential-rationality split and is the best current Lean target
  for the concrete extensive-form source proof.
- A one-sided source-completion certificate now matches the paper proof's
  uniqueness structure: prove "PBE drops at or after `q`" and "PBE does not
  drop before `q`", and Lean converts those two directions into the full core
  behavioral iff.
- The existing terminal-dynamic certificate now exposes a direct bridge to this
  one-sided certificate. This records that the already-certified full
  behavioral characterization implies the paper's two exclusion directions,
  while future source work can still target the weaker one-sided obligations.
- The sorted finite-schedule endpoint now also has a one-sided form:
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_one_sided_source_completion_of_clock_sorted_nodup`.
- An ex-post one-sided source-completion certificate now matches the paper's
  "best response regardless of beliefs" wording by requiring sequential
  rationality for every belief and then deriving the one-sided source endpoint.
- The paper interface exposes the sharper ex-post local-deviation finite
  schedule route as
  `theorem8_ex_post_local_deviation_finite_schedule_all_completed_source_completion`,
  where the completed ranks are exactly the sorted no-duplicate schedule.
- The recursive clock-sorted schedule premise now has concrete human-check
  helpers for `[]`, `rank :: tail`, `[rank]`, and `[rank, nextRank]`; this lets
  small paper-facing exact-drop schedules be checked by local threshold
  inequalities rather than by unfolding the recursive predicate manually.
- A source-extensive terminal-record checker is now available:
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game`.
  Its PBE predicate includes source sequential rationality, the concrete
  generated strategy history from the initial state to the audited terminal
  state, and terminality under the same strategy. The sorted finite-schedule
  endpoint
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`
  and its cold-start threshold-sorted specialization close the finite
  terminal-record instantiation without an external exact-history witness.
  The generic no-overshoot terminal-history endpoint also has a
  threshold-reached form,
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le`,
  which derives completed-rank inactivity from the terminal clock cutoff.
- The finite exact-record state-based source-extensive route is closed. Its
  cold-start state has exactly the displayed finite active ranks, so covering
  that finite active set gives all-ranks terminality for the state game rather
  than only completed-rank conclusions in the ambient `ℕ` cold-start state.
  The paper interface exposes this initial-state ledger as
  `theorem8_finite_active_exact_record_cold_start_state_ledger`: listed ranks
  are active, and unlisted ranks already carry exact finite `B*` records.
  The source-extensive endpoint is
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted`,
  and the belief-explicit version is
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted`.
  The checker-level PBE obligations are also exposed in the local form
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states_pbe_iff_one_step_best_response_drop_at_threshold_history_terminal`
  and its belief-explicit counterpart. The named-strategy trace forms
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states_pbe_iff_named_strategy_history_terminal`
  and
  `paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states_pbe_iff_named_strategy_history_terminal`
  are the cleaner review target when the paper checker should say "PBE means
  the named finite `B*` strategy plus generated history and terminality."
- `PaperInterface.lean` now has a human-facing finite-index schedule wrapper:
  `theorem8_strict_ordered_fin_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted`
  accepts `List (Fin n)` and translates it to the internal rank list. The
  direct completion check
  `theorem8_strict_ordered_fin_schedule_exact_record_final_state_no_active_of_threshold_sorted`
  shows that the displayed finite schedule leaves no active ranks in the
  finite exact-record state game. The complete-schedule check
  `theorem8_strict_ordered_complete_fin_schedule_displayed_ranks_active_then_inactive_of_threshold_sorted`
  additionally requires every displayed `Fin n` rank to appear in the schedule
  and proves that each displayed rank starts active and ends inactive. The
  named-PBE trace wrapper
  `theorem8_strict_ordered_fin_schedule_belief_source_extensive_named_pbe_trace_of_threshold_sorted`
  exposes the named finite `B*` PBE, generated history, terminality, and exact
  drop history without unpacking the full `∃!` theorem. The
  displayed formula wrapper
  `theorem8_strict_ordered_fin_schedule_belief_source_extensive_displayed_rank_formulas_of_threshold_sorted`
  states, for each displayed `Fin n` rank, the assigned slot and payment as the
  finite `B*` threshold formula.
- Bare `StrategyHistory` is formally too weak for exact terminal records:
  `paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_record`
  builds a terminal named-strategy history whose dropout record is one unit
  above the finite `B*` threshold, and
  `paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_not_exact_drop_history`
  proves that this generated terminal history is not an exact finite-`B*`
  dropout history. Future exact-record work should therefore target exact-drop
  histories, no-overshoot histories, or a stricter source transition relation
  that prevents clock overshoot at dropout.
- The paper interface now exposes the reusable ordinary-history bridge
  `theorem8_strategy_history_to_exact_drop_history_of_no_overshoot_drop_steps`
  and the no-overshoot terminal-record audit
  `theorem8_no_overshoot_terminal_record_eq_threshold_of_inactive`. Together
  these isolate the source-side timing fact needed to turn generalized-English
  histories into exact finite `B*` terminal records.
- The tighter local source-history route is also exposed directly:
  `theorem8_no_overshoot_strategy_history_to_strategy_history`,
  `theorem8_no_overshoot_strategy_history_to_exact_drop_history`,
  `theorem8_no_overshoot_strategy_history_terminal_records_eq_thresholds`, and
  `theorem8_no_overshoot_strategy_history_terminal_record_outcome_eq_bstar`.
  The constructor
  `theorem8_no_overshoot_terminal_certificate_of_strategy_history` packages
  such a raw history, terminality, and initial activity into the certificate
  expected by the source-extensive completed-rank and all-terminal endpoints.
  The direct-inactivity wrapper
  `theorem8_no_overshoot_strategy_history_source_extensive_completed_rank_conclusion`
  applies that constructor when the source proof already knows final inactivity
  on the completed ranks. The one-stop completed-threshold wrapper
  `theorem8_no_overshoot_strategy_history_source_extensive_completed_threshold_conclusion`
  uses terminal-clock threshold checks instead. The trace-refined completed-rank
  wrappers are
  `theorem8_no_overshoot_strategy_history_source_extensive_trace_completed_rank_conclusion`
  and
  `theorem8_no_overshoot_strategy_history_source_extensive_trace_completed_threshold_conclusion`;
  these additionally expose the named strategy, generated history,
  terminality, and exact-drop history. The belief-explicit trace counterparts
  are
  `theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_completed_rank_conclusion`,
  `theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_completed_threshold_conclusion`,
  and
  `theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`.
  The source-extensive all-rank trace counterpart is
  `theorem8_no_overshoot_strategy_history_source_extensive_trace_all_terminal_vcg_conclusion`.
  Use this route when the source proof can attach no-overshoot evidence to each
  realized dropout transition instead of proving a global predicate over all
  possible dropout states.
- The source-transition strengthening
  `theorem8_clock_disciplined_strategy_history_to_exact_drop_history` shows one
  sufficient route: if every clock advance stays below all active ranks'
  finite `B*` thresholds, then the named-strategy history is exact.
  The forgetful bridge
  `theorem8_clock_disciplined_strategy_history_to_strategy_history` supplies the
  ordinary generated-history obligation without needing the initial no-overshoot
  premise.
  `theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history`
  then packages a terminal disciplined history for the existing source-extensive
  endpoint family.
  Use
  `theorem8_clock_disciplined_terminal_history_source_extensive_completed_threshold_conclusion`
  when the source proof already has terminality and completed-threshold
  evidence and should go straight to the source-extensive PBE conclusion.
  The finite-schedule bridge
  `theorem8_clock_sorted_schedule_to_clock_disciplined_history` connects
  clock-sorted no-duplicate schedules to that source-transition relation under
  the active-unscheduled-threshold premise; singleton and pair shortcuts expose
  the common small schedule cases directly.

## Remaining source gap

The remaining non-reduced-form theorem is not another payment-algebra fact. It
is the concrete generalized-English extensive-form argument:

1. For finite schedule instances, use the source-extensive terminal-record
   endpoint above; the generated history and terminality are now inside PBE.
   When the paper instance has a genuinely finite displayed bidder/rank set,
   prefer the finite exact-record state-game wrappers
   `theorem8_strict_ordered_finite_active_exact_record_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted`,
   `theorem8_strict_ordered_finite_active_exact_record_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted`,
   or the `List (Fin n)` wrapper
   `theorem8_strict_ordered_fin_schedule_belief_source_extensive_displayed_rank_formulas_of_threshold_sorted`.
   If the source proof first needs only the schedule-generated reachability and
   exact-record objects, use `theorem8_clock_sorted_schedule_history_obligations`.
   Do not try to get an all-ranks-inactive conclusion from a finite cold-start
   schedule in the current `ℕ`-rank model:
   `theorem8_cold_start_clock_sorted_finite_schedule_leaves_active_unscheduled_rank`
   proves that some unscheduled rank remains active. Use completed-rank
   conclusions for finite checks, or introduce a finite-bidder source model.
2. For the fully general paper statement, prove the source-side no-overshoot
   timing fact for the real transition relation, then apply
   `theorem8_strategy_history_to_exact_drop_history_of_no_overshoot_drop_steps`.
   At the single-transition level,
   `theorem8_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot`
   is the intended local bridge: once source semantics prove a realized
   named-strategy dropout did not overshoot, the recorded dropout price is
   exactly the finite `B*` threshold.
   Bare `StrategyHistory` cannot imply exact records; the overshoot witness
   above is a formal counterexample. If the real transition relation is encoded
   through clock-disciplined advances, the target theorem is
   `theorem8_clock_disciplined_strategy_history_to_exact_drop_history`, or
   `theorem8_clock_disciplined_strategy_history_obligations` when the source
   proof must feed both the generated-history and exact-record obligations; for
   finite schedules, use
   `theorem8_clock_sorted_schedule_to_clock_disciplined_history` first.
   When the proof only needs a per-rank terminal-record equality from a
   clock-disciplined trace, use
   `theorem8_clock_disciplined_strategy_history_final_record_eq_threshold`; for
   histories beginning at the paper cold-start state, use
   `theorem8_cold_start_clock_disciplined_strategy_history_final_record_eq_threshold`
   to discharge the initial no-overshoot premise automatically.
   For source histories that start at the cold-start state, use
   `theorem8_cold_start_clock_disciplined_terminal_history_source_trace_full_conclusion`
   when the review target is unique PBE plus named-strategy/generated-history/
   terminality/exact-record trace. Use
   `theorem8_cold_start_clock_disciplined_terminal_history_source_trace_full_completed_rank_conclusion`
   when the same route should also display completed-rank terminal-record
   formulas. Both endpoints discharge the initial no-overshoot premise from
   the cold-start clock `-1` and nonnegative finite `B*` thresholds, while
   still requiring the source proof to supply the clock-disciplined transition
   history and terminality.
   The source-extensive variant
   `theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_trace_completed_threshold_conclusion`
   uses the same cold-start timing discharge while keeping generated-history
   and terminality evidence inside the checker PBE predicate.
   If the source proof identifies completed ranks by final inactivity rather
   than by terminal-clock threshold inequalities, use
   `theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_trace_completed_rank_conclusion`.
   The belief-explicit source-extensive variant
   `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion`
   also keeps that generated-history and terminality evidence inside the
   belief object.
   Its direct-inactivity analogue is
   `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_rank_conclusion`.
   When the clock-disciplined terminal state has no active ranks left, the
   direct all-terminal endpoints are
   `theorem8_clock_disciplined_terminal_history_source_extensive_outcome_eq_vcg`,
   `theorem8_clock_disciplined_terminal_history_source_extensive_slot_payment_eq_vcg`,
   `theorem8_clock_disciplined_terminal_history_source_extensive_utility_eq_vcg`,
   and the bundled endpoint
   `theorem8_clock_disciplined_terminal_history_source_extensive_all_terminal_vcg_conclusion`.
   For cold-start source histories, the all-terminal cold-start wrappers are
   `theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_all_terminal_vcg_conclusion`,
   `theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_trace_all_terminal_vcg_conclusion`,
   and the belief-explicit trace endpoint
   `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`;
   these derive the initial timing/activity facts from the paper cold-start
   state and leave only the clock-disciplined transition history, terminality,
   and all-ranks-inactive terminal condition.
3. Instantiate concrete belief consistency for the named strategy. For the
   audited no-overshoot terminal-record checker, this is now explicit:
   `theorem8_belief_source_extensive_named_belief_consistent`,
   `theorem8_belief_source_extensive_named_belief_sequentially_rational`, and
   `theorem8_belief_source_extensive_named_strategy_pbe_from_named_belief`
   expose the canonical belief that carries the generated history and
   terminality proof for the named finite `B*` strategy.
4. Instantiate the source-shaped sequential-rationality target
   `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement`
   for the real generalized-English game: reachable states and off-path states
   both reduce to the state-local one-step payoff comparison, plus the paper's
   drop-at-threshold convention.
   In `PaperInterface.lean`, `sourceSequentialGame`,
   `theorem8_source_sequential_pbe_iff_source_target`, and
   `theorem8_source_sequential_pbe_iff_named_strategy` expose this compact
   checker directly for review; use
   `theorem8_source_sequential_pbe_iff_one_step_best_response_and_drop_at_threshold`
   for the one-step/tie-break form.
   For the source-extensive target, use
   `paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_iff_local_deviation_history_terminal`
   to split the obligation into local deviation, generated history, and
   terminality. The terminal-record checker also exposes
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_local_deviation_history_terminal`.
   To project obligations back out of an accepted checker PBE, use
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_history_terminal_exact_drop_history`.
   If the terminal state has no active ranks, use
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_outcome_eq_vcg_of_no_overshoot`
   for the all-terminal VCG-outcome conclusion,
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_slot_payment_eq_vcg_of_no_overshoot`
   for rankwise slot/payment equality,
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_slot_payment_eq_vcg_of_no_overshoot`
   for the unique-PBE componentwise version, or
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_utility_eq_vcg_of_no_overshoot`
   when the payoff statement is the desired endpoint. Use
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_all_terminal_vcg_conclusion_of_no_overshoot`
   when the paper-facing check should bundle outcome, rankwise slot/payment,
   and bidder utility equality in one unique-PBE theorem.
   With an audited no-overshoot terminal certificate, the checker reduces further
   to
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_local_deviation`.
   The same statement is available in one-step/tie-break form as
   `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold`.
5. Use
   `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation`
   to reuse the existing local-deviation endpoints after the source reachable
   and off-path obligations are proved.
   At the source-completion layer, package the game-level iff with
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_certificate_of_source_iff`;
   then convert by
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_core_source_completion_certificate_of_source_sequential_rationality`.
   For direct PBE behavior checks from the source-shaped core certificate, cite
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_named_strategy_pbe`,
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_pbe_strategy_eq_named`,
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_exists_unique_named_pbe`,
   or
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_pbe_outcome_eq_vcg`.
6. Feed those narrowed core PBE facts into the core/finite exact-history
   source-completion certificate. Slot/payment VCG equality is no longer a
   separate source obligation.
   When the concrete source proof has belief consistency, the game-level
   reachable/off-path sequential-rationality iff, generated PBE histories,
   no-overshoot timing, and terminal-record outcome/VCG identifications as
   separate facts, use
   `theorem8_source_iff_histories_no_overshoot_full_conclusion` directly.
   If the terminal side is already packaged as a no-overshoot terminal/dynamic
   certificate, use
   `theorem8_no_overshoot_terminal_dynamic_source_iff_full_conclusion`; that
   wrapper avoids separate generated-history and global no-overshoot premises.
   For completed-rank conclusions through the same route, use
   `theorem8_no_overshoot_terminal_dynamic_source_iff_completed_threshold_conclusion`
   or
   `theorem8_no_overshoot_terminal_dynamic_source_iff_utility_eq_bstar_of_completed_threshold`.
   For the trace-full source-shaped route where completed ranks are known by
   final inactivity rather than by terminal-clock inequalities, use
   `theorem8_no_overshoot_terminal_dynamic_trace_full_completed_rank_conclusion`.
   If the source proof has a clock-disciplined trace instead of a prebuilt
   no-overshoot terminal/dynamic certificate, use
   `theorem8_clock_disciplined_terminal_history_source_iff_full_conclusion`;
   for finite completed-rank formulas, use
   `theorem8_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion`.
   If that clock-disciplined trace starts at the cold-start state, use
   `theorem8_cold_start_clock_disciplined_terminal_history_source_iff_full_conclusion`
   or
   `theorem8_cold_start_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion`
   to avoid restating initial timing/activity facts.
   For finite schedules, the direct endpoint is now
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_clock_sorted_nodup`.
   If the source proof has not explicitly built the source-shaped core
   certificate, use the one-stop theorem
   `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_source_iff_clock_sorted_nodup`.

## Next proof route

The reusable finite-schedule constructor route is closed for the audited
source-extensive terminal-record checker, and the finite exact-record
state-game route is closed for genuinely finite displayed rank sets. The next
Lean target should be the fully general concrete extensive-form proof: belief
consistency, source-shaped sequential rationality for arbitrary
reachable/off-path states, and the source no-overshoot timing argument that
feeds the exact-record bridge. A separate finite-bidder source model would also
be useful, but it should be introduced only if the paper-facing finite-index
state-game wrapper is not enough for review.

Closed finite-schedule construction route:

Informal statement:

Given a finite list or finset of ranks, if the clock starts below each rank's
finite `B*` threshold and the selected ranks are processed in nondecreasing
threshold order, repeatedly:

1. advance the clock to the current rank's threshold,
2. record that active rank's dropout,
3. preserve prior dropout records,
4. preserve exactness by transitivity.

The result should be an exact-drop history from the initial state to a final
state where every scheduled rank is inactive and has terminal record equal to
its finite `B*` threshold.

Likely Lean shapes:

- A list-based constructor is probably easier than a finset constructor because
  the source auction has an order of events.
- The constructor should carry hypotheses:
  each scheduled rank is active when processed, or stronger no-duplicate ranks
  plus all scheduled ranks initially active.
- If the schedule is threshold-sorted, clock monotonicity follows from the
  sorted-threshold hypothesis.
- Do not try to solve sorting and no-tie issues in the same theorem. First prove
  a schedule certificate theorem with explicit clock monotonicity and active
  premises.

Completed Lean endpoint:

```lean
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_history_append_single
    ...
```

This composes an existing exact history ending at `state` with one more single
exact drop from `state` to the new final state.

Completed Lean endpoint:

```lean
inductive PaperTheorem8BStarRankedThresholdExactDropSchedule ...
```

This recursive list predicate says the next rank is active, the clock can
advance to its threshold, and the tail schedule starts from the post-drop state.
It currently proves conversion to exact history, exact terminal records for
scheduled ranks, and final inactivity for scheduled ranks.

Completed Lean endpoint:

```lean
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_finset_outcome_conclusion
    ...
```

This combines the schedule terminal-record and inactivity facts with the
existing finite completed-rank outcome theorem. The input is a list schedule
plus a finite set of ranks known to be included in the schedule list.

Completed Lean endpoints:

```lean
structure PaperTheorem8BStarRankedThresholdStrictOrderedFiniteScheduleTerminalDynamicCertificate
theorem paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_terminal_dynamic_pbe_with_terminal_record_conclusion
structure PaperTheorem8BStarRankedThresholdStrictOrderedFiniteScheduleSourceCompletionCertificate
theorem paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_completion_exists_unique_pbe_with_terminal_record_conclusion
```

These are now the cleanest finite paper-facing boundary: if the source proof
supplies the PBE obligations and an ordered exact-drop schedule completing the
finite rank set, Lean gives unique PBE plus terminal-record payment/VCG-tail
conclusions on that finite set.

Completed Lean endpoint:

```lean
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_from_sorted_thresholds
    ...
```

Implemented as:

```lean
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
    ...
```

This removes the manual stepwise schedule premises by deriving them from a
clock-sorted threshold hypothesis, no duplicates, and initial activity.
The audit surface also exposes `nil`, `cons_iff`, `singleton`, and `pair`
clock-sorted helper lemmas, so concrete finite examples can discharge the
sortedness hypothesis directly from the displayed threshold inequalities.

Completed Lean endpoint:

```lean
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_source_completion_of_clock_sorted_nodup
    ...
```

Implemented as:

```lean
theorem paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_completion_of_clock_sorted_nodup
    ...
```

This packages the sorted/no-duplicate schedule constructor directly into the
finite schedule source-completion endpoint, so the source side only supplies PBE
obligations, the completed finite rank set, the ordered rank list, final-state
equality, and sorted/no-duplicate facts. Initial activity comes from the
terminal-history certificate.

Next proof target:

Do not add more finite-schedule or outcome plumbing unless it removes a
concrete source-history premise needed by the full PBE proof. The exact
source-history layer is strong enough for finite scheduled instances; the hard
gap is now the arbitrary-history generalized-English PBE proof.

## Source-PBE obligations after the schedule layer

After the exact schedule is available, the remaining hard proof is the PBE
argument. The useful way to attack it is not to expand all game theory at once:

- Define the concrete belief object only as richly as needed for the source
  proof.
- Prove a reachability/history invariant for named-strategy histories.
- For generated source histories with no-overshoot timing, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_core_source_completion_all_pbe_outcome_eq_vcg_of_histories_no_overshoot`
  or, from the reachable/off-path certificate,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_all_pbe_outcome_eq_vcg_of_histories_no_overshoot`.
  Use the matching `...all_pbe_utility_eq_vcg_of_histories_no_overshoot`
  wrapper for the paper's payoff wording.
  To enter the existing full source-completion endpoint family, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_completion_certificate_of_source_sequential_rationality_and_histories_no_overshoot`.
  To close the full equilibrium statement directly, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_histories_no_overshoot_exists_unique_pbe_with_full_conclusion`.
  If the source work has built the no-overshoot terminal-dynamic certificate,
  use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion`
  instead.
  For finite completed-rank checks, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion`
  and prove inactivity only for the completed rank set.
  Use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_terminal_record_utility_eq_bstar_of_mem`
  when the finite paper-facing check is payoff equality rather than the
  displayed slot/payment formulas.
- For the strict ordered local-deviation checker with a no-overshoot terminal
  history, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_ex_post_local_deviation_core_source_completion_pbe_history_obligations_of_no_overshoot_terminal_history`.
  It turns any PBE strategy into the already-audited no-overshoot terminal
  history plus exact-drop history after the checker identifies the PBE strategy
  with the named finite `B*` strategy.
- For a compact source-shaped checker with concrete terminal records as the
  outcome map, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game`.
  Its PBE predicate is the reachable/off-path source statement, and exact or
  no-overshoot terminal histories with all ranks inactive give direct
  outcome-equals-VCG, utility-equals-VCG, and bundled unique-PBE
  outcome/utility endpoints. For finite paper
  checks, use the completed-rank slot/payment and utility endpoints instead of
  proving every ambient rank inactive; use the matching unique-PBE packages
  when the paper-facing statement should include equilibrium uniqueness. When
  the review target is the paper's displayed formula rather than equality to
  `G.vcgOutcome`, use the completed-rank paper-conclusion endpoints and their
  unique-PBE wrappers; use the threshold-reached variants when the terminal
  clock cutoff is easier to check than an explicit inactivity proof.
- Use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_ex_post_local_deviation_core_source_completion_pbe_completed_rank_terminal_record_paper_conclusion_of_no_overshoot_terminal_history`
  when the paper-facing obligation is the completed-rank slot/payment,
  VCG-tail accounting, and payment interval statement for that concrete
  checker; it avoids restating the all-PBE generated-history premise.
- Use the
  `...pbe_completed_rank_terminal_record_paper_conclusion_of_no_overshoot_terminal_history_completed_threshold_le`
  variant when completed ranks are checked by terminal-clock threshold
  inequalities instead of a separate inactivity proof.
- Use the matching
  `...exists_unique_pbe_with_completed_rank_terminal_record_paper_conclusion_of_no_overshoot_terminal_history_completed_threshold_le`
  theorem when the audit target is unique PBE plus those displayed
  completed-rank formulas for the concrete checker.
- Use
  `...pbe_ordered_terminal_record_paper_conclusion_of_no_overshoot_terminal_history`
  and the matching
  `...exists_unique_pbe_with_ordered_terminal_record_paper_conclusion_of_no_overshoot_terminal_history`
  when the terminal state has every rank inactive and the audit target is the
  all-rank ordered paper-conclusion form. The paper-facing wrapper is
  `theorem8_ex_post_no_overshoot_terminal_history_source_completion_ordered_terminal_record_conclusion`.
- Use
  `theorem8_ex_post_no_overshoot_terminal_history_source_completion_pbe_iff_named_strategy`
  first when the audit target is just the behavioral uniqueness checkpoint for
  the same concrete checker.
- Use
  `paper_theorem8_bstar_ranked_threshold_named_strategy_one_step_best_response`
  as the local one-step deviation inequality for the named finite `B*`
  strategy, rather than re-proving the payoff comparison from the raw
  indifference lemmas.
- Use
  `paper_theorem8_bstar_ranked_threshold_one_step_best_response_at_state`
  when the proof is phrased at a concrete generalized-English history state.
  The global predicate is equivalent to all state-local obligations by
  `paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement_iff_forall_state`.
- Use
  `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement`
  as the current source-shaped target. It splits sequential rationality into
  reachable-state and off-path-state one-step obligations plus threshold
  tie-breaking, and
  `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation`
  converts it back to the existing local-deviation theorem stack. The named,
  strict, and strict-ordered finite `B*` strategies already have wrappers:
  `paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality`,
  `paper_theorem8_bstar_ranked_threshold_strict_named_strategy_source_sequential_rationality`,
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_named_strategy_source_sequential_rationality`.
- The source-completion layer now has
  `PaperTheorem8BStarRankedThresholdStrictOrderedSourceSequentialRationalityCoreSourceCompletionCertificate`.
  Its constructor
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_certificate_of_source_iff`
  takes concrete belief consistency and a game-level iff between
  `isSequentiallyRational` and the source-shaped reachable/off-path predicate.
  The named-strategy sequential-rationality field is discharged automatically
  from the strict finite `B*` source theorem.
  Use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_core_source_completion_certificate_of_source_sequential_rationality`
  to return to the existing local-deviation endpoint family.
- For isolated checker tests, use
  `paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_source_sequential`,
  `paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_local_deviation`,
  and
  `paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_named_strategy`.
  These are not the real source extensive form, but they keep the
  reachable/off-path predicate as the visible PBE surface.
- For the compact source-shaped dynamic game itself, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate`.
  It is the constructed-outcome certificate whose sequential-rationality
  predicate is definitionally the reachable/off-path source statement, so the
  belief-consistency and source-iff obligations are no longer external for
  this checker. The direct sorted-schedule full-conclusion endpoints are
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`.
- For terminal-record paper formulas from a finite schedule, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`.
  It constructs the no-overshoot terminal history and exact finite `B*`
  records from sorted no-duplicate schedule data, so this route does not need a
  separately supplied exact-history witness. In cold-start strict ordered
  paper instances, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_strict_ordered_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`
  to replace recursive clock-sortedness with adjacent threshold sortedness and
  a last-threshold unscheduled comparison.
- Prefer the source-extensive versions when the checker should prove the
  generated history and terminality as part of PBE itself:
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`
  and
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_strict_ordered_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`.
  For a prebuilt no-overshoot terminal history, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot`
  or the terminal-clock variant
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le`.
  In `PaperInterface.lean`, these appear as
  `theorem8_terminal_record_source_extensive_schedule_completed_rank_conclusion`
  and
  `theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_conclusion`;
  the prebuilt-history wrappers are
  `theorem8_no_overshoot_terminal_record_source_extensive_completed_rank_conclusion`
  and
  `theorem8_no_overshoot_terminal_record_source_extensive_completed_threshold_conclusion`.
- For the final finite scheduled proof route, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_clock_sorted_nodup`.
  It starts from the source-shaped core certificate plus final-state equality,
  sorted no-duplicate schedule data, and completed-rank inclusion, then returns
  unique PBE with the finite terminal-record formulas.
  If the available source proof facts are concrete belief consistency and the
  game-level sequential-rationality iff, use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_source_iff_clock_sorted_nodup`
  instead; it constructs the source-shaped core certificate internally.
  If the proof has the ex-post local-deviation certificate already, use
  `theorem8_ex_post_local_deviation_finite_schedule_all_completed_source_completion`
  for the paper-facing all-scheduled schedule version.
  If the proof has an annotated no-overshoot terminal history rather than a
  finite schedule object, use
  `theorem8_ex_post_no_overshoot_terminal_history_source_completion_completed_threshold_conclusion`
  for the unique-PBE terminal-record conclusion, or
  `theorem8_ex_post_no_overshoot_terminal_history_source_completion_utility_eq_bstar_of_completed_threshold`
  for completed-rank payoff equality.
  When the intended checker is already the compact source-shaped dynamic game,
  use
  `theorem8_source_sequential_no_overshoot_terminal_history_source_completion_completed_threshold_conclusion`
  and
  `theorem8_source_sequential_no_overshoot_terminal_history_source_completion_utility_eq_bstar_of_completed_threshold`;
  these specialize the generic no-overshoot source-completion theorem without
  separately supplying a source-iff or belief-consistency proof.
  For the full source-shaped terminal-history conclusion when the annotated
  terminal certificate is the source of truth for the local model, use
  `theorem8_source_sequential_no_overshoot_terminal_history_full_conclusion_of_terminal_model_assumptions`;
  it upgrades that local model with the strict click, ordered value, and strict
  tail-payment assumptions and removes the separate model-equality proof.
  For the trace-full review form of the same source-shaped route, use
  `theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_threshold_conclusion`.
  The terminal-local trace form
  `theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_threshold_conclusion_of_terminal_model_assumptions`
  gives the same named-strategy, generated-history, terminality, exact-record,
  and completed-rank formula bundle without a separate model-equality proof.
  The finite source boundary itself is exposed in `PaperInterface.lean` as
  `theorem8_ex_post_finite_source_sequential_rationality_iff_local_deviation`,
  `theorem8_ex_post_finite_source_named_strategy_sequentially_rational_for_all_beliefs`,
  and
  `theorem8_ex_post_finite_source_named_strategy_local_deviation_of_one_step_best_response`.
  If the proof already has the all-rank ex-post local-deviation source object
  plus an exact-drop history, the paper-facing wrappers are
  `theorem8_ex_post_local_deviation_exact_history_source_obligations`,
  `theorem8_ex_post_local_deviation_exact_history_source_terminal_record_outcome_eq_bstar`,
  `theorem8_ex_post_local_deviation_exact_history_source_full_conclusion_terminal_record_outcome_eq_bstar`,
  and
  `theorem8_ex_post_local_deviation_exact_history_source_terminal_record_utility_eq_bstar`.
  In cold-start threshold-sorted schedule checks, use
  `theorem8_ex_post_local_deviation_cold_start_threshold_sorted_all_completed_source_completion`
  to construct that source certificate internally.
- Use
  `paper_theorem8_bstar_ranked_threshold_named_strategy_off_threshold_strict_best_response`
  when the proof needs the strict off-threshold exclusion directions matching
  the paper's Step 1 and Step 2.
- For the dynamic-game lift, target the one-step bridge field in
  `PaperTheorem8BStarRankedThresholdOneStepBestResponseDynamicGameExtensionalOutcomeCertificate`
  first. It is a cleaner obligation than proving sequential rationality
  directly from the full local-optimality statement.
- For behavioral PBE characterization, prove that every PBE strategy satisfies
  the one-step best-response predicate and the at-threshold drop tie-breaking
  convention, then apply
  `paper_theorem8_bstar_ranked_threshold_strategy_iff_of_one_step_best_response_and_drop_at_threshold`
  instead of reproving cutoff behavior from scratch.
  Human-facing versions of the Step 1/Step 2 local payoff inequalities are
  `theorem8_source_step1_dropping_after_q_strictly_better` and
  `theorem8_source_step2_waiting_before_q_strictly_better`.
  If the proof needs the displayed algebra around the indifference price `q`,
  use the paper-interface wrappers
  `theorem8_source_q_affine_eq`, `theorem8_source_q_empty_history_eq`,
  `theorem8_source_q_continuous_value`,
  `theorem8_source_q_injective_value`,
  `theorem8_source_q_mono_lastDropout`, and
  `theorem8_source_q_strict_mono_lastDropout`.
- The current cleanest behavioral target is therefore the tie-break dynamic
  certificate, not the older core certificate: prove PBE one-step optimality
  and PBE threshold tie-breaking, then use
  `paper_theorem8_bstar_ranked_threshold_one_step_best_response_extensional_outcome_certificate_of_tie_break`
  to recover the existing endpoints.
- At source-completion level, target
  `PaperTheorem8BStarRankedThresholdStrictOrderedOneStepTieBreakCoreSourceCompletionCertificate`.
  It derives the existing core source-completion certificate from belief
  consistency, the one-step-to-sequential-rationality lift, PBE one-step
  optimality, and PBE threshold tie-breaking.
- For the concrete strict ordered local-deviation checker, the one-step
  best-response premise is already discharged by
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_ex_post_local_deviation_core_source_completion_named_strategy_sequentially_rational_for_all_beliefs`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_ex_post_local_deviation_core_source_completion_named_strategy_local_deviation`.
  Do not spend the next pass manually threading the strict named one-step proof
  through that checker; use these endpoints and focus on the real
  generalized-English source lift.
- The same one-step/tie-break source certificate now also derives the paper's
  one-sided Step 1/Step 2 certificate, so the proof can be presented either as
  a cutoff iff or in the source proof's two exclusion directions.
- Package any remaining source-specific sequential-rationality proof as a
  theorem producing the source-shaped reachable/off-path predicate above, then
  convert to local-deviation by the iff theorem rather than duplicating the
  cutoff proof.
  The source-shaped checker also has
  `paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold`
  when the proof is stated directly as one-step optimality plus threshold
  tie-breaking. For the terminal-record source-shaped checker, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold`.
- For the source-extensive proof surface, use
  `paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_iff_local_deviation_history_terminal`
  as the local target: one local-deviation theorem, one generated-history
  theorem, and one terminality theorem are enough to enter the source-extensive
  checker. At the checker level, the matching PBE iff is
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_local_deviation_history_terminal`.
  For the finite exact-record state game, use
  `theorem8_source_extensive_state_game_pbe_iff_one_step_tiebreak_history_terminal`
  or
  `theorem8_belief_source_extensive_state_game_pbe_iff_one_step_tiebreak_history_terminal`;
  these show that one-step best response, threshold tie-breaking, generated
  history, and terminality are precisely the PBE obligations for the displayed
  finite state game. If the reviewer wants the named-strategy reading directly,
  use
  `theorem8_source_extensive_state_game_pbe_iff_named_strategy_history_terminal`
  or
  `theorem8_belief_source_extensive_state_game_pbe_iff_named_strategy_history_terminal`.
  The belief-explicit variant is
  `paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_local_deviation_history_terminal`;
  prefer it when auditing the actual PBE belief-consistency boundary, because
  the belief object carries the generated history and terminality proof and
  consistency checks that it belongs to the strategy under review.
  The belief-explicit checker also exposes the local behavioral target as
  `paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold`.
  For an audited no-overshoot terminal certificate, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_local_deviation`
  to avoid re-threading generated history and terminality.
  The corresponding belief-explicit shortcut is
  `paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_local_deviation`.
  For sorted finite schedules, the belief-explicit one-stop endpoint is
  `paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`,
  exposed in `PaperInterface.lean` as
  `theorem8_belief_source_extensive_schedule_trace_completed_conclusion`.
  For finite displayed rank sets, use
  `theorem8_strict_ordered_fin_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted`
  or
  `theorem8_strict_ordered_fin_schedule_belief_source_extensive_displayed_rank_formulas_of_threshold_sorted`
  to avoid manual natural-number rank bookkeeping.
  For all-terminal conclusions, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_all_terminal_vcg_conclusion_of_no_overshoot`
  or the paper-interface wrapper
  `theorem8_belief_source_extensive_all_terminal_vcg_conclusion`; if the source
  route starts from a clock-disciplined terminal history, use
  `theorem8_clock_disciplined_terminal_history_belief_source_extensive_all_terminal_vcg_conclusion`.
  When the reviewer should also see the PBE's named-strategy identity,
  generated source history, terminality, and exact dropout records, use the
  trace-refined belief-explicit endpoint
  `theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`.
  For the same all-terminal trace from the paper cold-start state, use
  `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`.
  If the same clock-disciplined route only needs completed-rank paper formulas,
  use
  `theorem8_clock_disciplined_terminal_history_belief_source_extensive_completed_threshold_conclusion`
  or the trace-refined
  `theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion`.
  For completed-rank paper formulas from a no-overshoot terminal history, use
  `theorem8_no_overshoot_terminal_record_belief_source_extensive_completed_threshold_conclusion`
  or, when the generated source-history trace should be visible,
  `theorem8_no_overshoot_terminal_record_belief_source_extensive_trace_completed_threshold_conclusion`.
  If the proof is organized around Step 1/Step 2 behavior, use
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold`.
- Prove PBE uniqueness by translating any PBE action at a state into the
  already-formal threshold iff statement.
- Use
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_completion_certificate_of_core`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_core_source_completion_of_clock_sorted_nodup`
  to recover the full finite source-completion endpoint; do not try to prove
  PBE-to-VCG slot/payment equality separately.
- For behavioral uniqueness, target
  `PaperTheorem8BStarRankedThresholdStrictOrderedOneSidedSourceCompletionCertificate`
  rather than the full iff directly. The two fields correspond to Step 1 and
  Step 2 of the paper proof.
- For the ex-post claim, target
  `PaperTheorem8BStarRankedThresholdStrictOrderedExPostOneSidedSourceCompletionCertificate`;
  it is the current closest endpoint to the source theorem statement.

## Audit discipline

Whenever a named paper result is truly closed, update:

- `PostPaperAudit.lean`
- `README.md`
- `POST_PAPER_AUDIT_REPORT.md`
- `FINAL_VALIDATION_REPORT.md`
- `DependencyDAG.tex` if the high-level dependency/caveat picture changes

Do not mark Theorem 8 complete until the concrete source PBE obligations and
finite exact source history are instantiated, not merely represented as
certificate fields.
