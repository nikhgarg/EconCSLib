# Final Validation Report: EOS07GSP

Date: 2026-05-16

## Verdict

This paper is not yet fully formalized in Lean. The current folder has a compiling
post-paper audit ledger and strong paper-facing endpoints for Sections 2.2--2.3,
Theorem 7, and finite/no-overshoot/clock-disciplined source routes for Theorem
8. The remaining gap is the unconstrained generalized-English source game:
concrete belief consistency, the game-level source sequential-rationality iff,
and exact terminal-record generation when no schedule, no-overshoot, or
clock-discipline evidence is supplied.

## Current handoff note

Start with `START_HERE_NEXT_AGENT.md` before continuing Theorem 8. It is the
short pickup file for the 2026-05-16 pause and points to the live proof plan,
audit report, and older detailed handoff. The latest source obligation
additions expose direct source-iff, no-overshoot terminal/dynamic, and
clock-disciplined terminal-history wrappers in `PaperInterface.lean`. The
latest theorem edits compiled under `lake build EOS07GSP`; rerun that target
after any further Lean edits.

## Source version

- Paper: *Internet Advertising and the Generalized Second-Price Auction:
  Selling Billions of Dollars Worth of Keywords*
- Authors: Benjamin Edelman, Michael Ostrovsky, and Michael Schwarz
- Local source: NBER Working Paper 11765, November 2005
- Publication citation: AER 2007
- Paper folder: `papers/EOS07GSP`
- Human-facing theorem files: `papers/EOS07GSP/PaperInterface.lean`,
  `papers/EOS07GSP/MainTheorems.lean`, `papers/EOS07GSP/PostPaperAudit.lean`
- DAG artifact: `papers/EOS07GSP/DependencyDAG.tex`

On 2026-05-16 the local `EOS07GSP.pdf` and `EOS07GSP.txt` cache was refreshed
against `https://www.nber.org/papers/w11765.pdf`; both matched the online NBER
download exactly. A Stanford-hosted later/final PDF was inspected as a
cross-check and renumbers the analogous main results as Theorems 1--2, so this
folder keeps the NBER numbering used by the cached source. The DAG inventory
therefore starts at Remarks 1--3 before Definition 4.

## Current Lean coverage

| Paper item | Status | Human verification entry point |
|---|---|---|
| GSP non-truthfulness and running examples | formalized | `PaperInterface.lean` counterexample and running-example declarations |
| Remark 1, same-bid GSP payment dominates VCG payment, `EOS07GSP.txt:372` | formalized | generic ranked VCG-tail induction plus concrete GSP/VCG revenue comparison |
| Remark 2, VCG truthfulness, `EOS07GSP.txt:388` | formalized with certificate | `PaperInterface.lean` exposes the generic VCG position-mechanism truthfulness theorem from reported-welfare maximization, the externality-tax utility identity, and own-report-independent taxes |
| Remark 3, GSP is not truthful, `EOS07GSP.txt:390` | formalized | `PaperInterface.lean` GSP counterexample declaration |
| Definition 4, locally envy-free equilibrium, `EOS07GSP.txt:443` | formalized | locally-envy-free audit declarations |
| Lemma 5, locally envy-free equilibrium gives stable assignment, `EOS07GSP.txt:465` | formalized with documented caveat | stable-assignment bridge audit declarations |
| Lemma 6, stable assignment gives locally envy-free outcome, `EOS07GSP.txt:466` | formalized with documented caveat | stable-to-slot-envy-free audit declarations |
| Theorem 7, `B*` locally envy-free equilibrium and revenue comparison, `EOS07GSP.txt:481` | conditional | `PaperInterface.lean` ranked `B*` paper conclusion plus canonical-tail audit declarations |
| Theorem 8, generalized-English unique PBE, `EOS07GSP.txt:539` | conditional, with finite/no-overshoot/clock-disciplined source routes closed | `PaperInterface.lean` source-iff, no-overshoot terminal/dynamic, clock-disciplined terminal-history, and source-extensive terminal-record endpoints |

## Important completed endpoints

- Theorem 7 now has a bundled endpoint showing that, under nonnegative values,
  the constructed ranked `B*` outcome itself has no positive transfers while
  retaining the revenue-minimality conclusion against no-positive-transfer
  comparison outcomes.
- Theorem 8 now has direct endpoints for named finite `B*` strategy PBE
  existence, standard `∃!` PBE uniqueness, PBE iff canonical strategy,
  pointwise PBE/named-strategy action equivalence, pairwise PBE action uniqueness, direct PBE strategy equality, direct PBE and named-strategy cutoff behavior including exact-drop-at-threshold plus before/after-threshold one-direction consequences, exact strategy and PBE not-drop iff complements, strict no-early-drop/drop-by-value behavior, concrete PBE and named-equilibrium behavior-region witnesses, PBE outcome
  equality with VCG, named-strategy VCG outcome, pairwise PBE outcome equality, and componentwise slot/payment equality with VCG, named-strategy slot/payment equality with VCG, pairwise PBE slot/payment equality.
- Theorem 8 now has concrete strategy-consistent generalized-English
  step/history wrappers: strategy-consistent histories refine concrete
  histories, dropped records are preserved, a finite-`B*`
  strategy-consistent step cannot newly drop a rank before its threshold bid,
  and the strongest strict ordered terminal-dynamic certificate exposes PBE
  terminal actions and concrete dropout records from the same local model.
- Theorem 8 source-proof algebra now includes topology-free unboundedness
  lemmas for both the scalar indifference price and the rank-indexed dropout
  price as value increases under positive affine and strict adjacent
  click-rate hypotheses.
- Theorem 8 local payoff accounting now has first-class continue/drop payoff
  definitions and a named one-step best-response theorem for the finite `B*`
  ranked-threshold strategy under the local-optimality certificate, plus an
  off-threshold strict best-response wrapper matching the paper's Step 1/Step 2
  exclusion directions. The same facts are exposed directly for strict and
  strict ordered source-facing certificates.
- Theorem 8 dynamic sequential-rationality lift now has a narrower one-step
  bridge certificate, so future source work can prove that the audited
  one-step best-response predicate implies the game-level sequential-rationality
  predicate and then reuse the existing local-optimality dynamic-game endpoints.
  Direct one-step bridge endpoints now also expose named-strategy PBE,
  unique-PBE, generic unique-PBE/VCG, arbitrary-PBE paper conclusions, and the
  named-strategy paper conclusion.
- Theorem 8 behavioral PBE characterization now has a local theorem: one-step
  best response plus the paper's at-threshold drop tie-breaking convention
  forces the finite `B*` cutoff rule and equality to the named finite `B*`
  strategy. The named finite `B*` strategy itself now exposes the
  drop-at-threshold tie-breaking fact directly.
- The strict off-threshold part is separated: one-step best response alone
  implies post-threshold dropping and pre-threshold non-dropping, leaving only
  exact-threshold tie-breaking as a separate behavioral convention.
- A separate cutoff-assembly theorem now combines any proof of strict
  off-threshold behavior with at-threshold drop tie-breaking to recover the
  finite `B*` cutoff rule and extensional equality to the named finite `B*`
  strategy.
- The dynamic behavioral PBE field now has a narrower one-step/tie-break
  certificate: prove PBE one-step best response and PBE at-threshold drop
  tie-breaking, and Lean derives the finite `B*` cutoff iff, unique PBE, and
  named-strategy paper conclusion.
- The PBE behavioral field is now also available through a source
  sequential-rationality certificate: prove that `isSequentiallyRational`
  implies local one-step best response and threshold tie-breaking, and Lean
  unpacks each PBE witness to derive the one-step/tie-break dynamic certificate.
  The reduced-form scaffold instantiates this certificate directly, validating
  the narrowed seam on a concrete checker while remaining explicitly separate
  from the source extensive-form auction.
- The source sequential-rationality obligation now has a sharper local-deviation
  certificate: prove `isSequentiallyRational` iff local one-step best response
  plus threshold tie-breaking. Lean derives the sequential-rationality,
  one-step/tie-break, one-sided, core, and full source-completion certificates
  from this equivalence. The reduced-form scaffold instantiates this sharper
  certificate as well.
- The paper interface now exposes the all-scheduled sorted finite-schedule
  endpoint for the ex-post local-deviation source route as
  `theorem8_ex_post_local_deviation_finite_schedule_all_completed_source_completion`.
- The paper interface also exposes the Step 1/Step 2 payoff comparisons,
  local `q` interval checks, and supporting affine/empty-history/continuity/
  injectivity/history-monotonicity `q` facts directly, so reviewers can inspect
  those proof-line inequalities without searching the audit ledger.
- The local-deviation target itself is now named by
  `paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement`,
  with named-strategy, cutoff-rule, and strategy-equality wrappers, so the
  source proof has a compact theorem target rather than a raw conjunction.
- The same local-deviation target now has an explicitly source-shaped
  reachable/off-path form:
  `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement`.
  Its state-local one-step component is
  `paper_theorem8_bstar_ranked_threshold_one_step_best_response_at_state`, the
  global/state-local equivalence is
  `paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement_iff_forall_state`,
  and
  `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation`
  converts the source-shaped target back to the existing local-deviation stack.
  Named, strict, and strict-ordered finite `B*` source wrappers are exposed for
  direct audit citation.
- The strict ordered source-completion layer now has
  `PaperTheorem8BStarRankedThresholdStrictOrderedSourceSequentialRationalityCoreSourceCompletionCertificate`.
  The constructor
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_rationality_core_source_completion_certificate_of_source_iff`
  only asks the future source proof for concrete belief consistency and a
  game-level iff between `isSequentiallyRational` and the source-shaped
  reachable/off-path predicate. Lean then converts this to the existing
  local-deviation core route via
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_core_source_completion_certificate_of_source_sequential_rationality`.
  The same source-shaped core certificate now also exposes direct
  named-strategy PBE, arbitrary-PBE strategy equality, unique-PBE, and
  arbitrary-PBE VCG-outcome endpoints without manual certificate conversion.
- The paper interface now exposes direct source-obligation endpoints for the
  May 16 boundary. `theorem8_source_iff_histories_no_overshoot_full_conclusion`
  consumes concrete belief consistency, the game-level reachable/off-path
  source iff, generated PBE histories, no-overshoot timing, and the terminal
  outcome/VCG identifications. The no-overshoot terminal/dynamic wrappers
  `theorem8_no_overshoot_terminal_dynamic_source_iff_full_conclusion`,
  `theorem8_no_overshoot_terminal_dynamic_source_iff_completed_threshold_conclusion`,
  and
  `theorem8_no_overshoot_terminal_dynamic_source_iff_utility_eq_bstar_of_completed_threshold`
  use the same source iff when the history evidence is already packaged. The
  clock-disciplined wrappers
  `theorem8_clock_disciplined_terminal_history_source_iff_full_conclusion` and
  `theorem8_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion`
  build that no-overshoot package from a disciplined terminal trace.
  The cold-start variants
  `theorem8_cold_start_clock_disciplined_terminal_history_source_iff_full_conclusion`
  and
  `theorem8_cold_start_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion`
  keep the same concrete belief-consistency/source-iff obligations while
  deriving the initial timing/activity facts from the cold-start state.
  For annotated no-overshoot terminal histories where the terminal certificate's
  local model is the source of truth,
  `theorem8_source_sequential_no_overshoot_terminal_history_full_conclusion_of_terminal_model_assumptions`
  upgrades that local model with the strict/ordered paper assumptions and avoids
  a separate local-model equality proof.
  Its trace-refined completed-rank counterpart
  `theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_threshold_conclusion_of_terminal_model_assumptions`
  exposes the named strategy, generated history, terminality, exact records, and
  displayed completed-rank formulas through the same terminal-local route.
- A standalone source-shaped checker,
  `paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game`,
  now exposes direct PBE iff source-shaped, PBE iff local-deviation, and PBE
  iff named-strategy endpoints. This is a compact checker for the new
  reachable/off-path predicate, not the full source extensive form.
  `PaperInterface.lean` exposes it as `sourceSequentialGame` with direct PBE
  iff source-target, named-strategy, and one-step/tie-break wrappers.
  Its strict ordered constructed-outcome certificate,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate`,
  discharges belief consistency and the source-shaped sequential-rationality
  iff by construction for that compact checker, with direct sorted-schedule
  full-conclusion endpoints including the no-overshoot variant.
  A terminal-record source-shaped checker now combines that PBE predicate with
  concrete terminal dropout records as the outcome map and exposes exact and
  no-overshoot outcome/utility equality to VCG when all ranks are inactive,
  including a one-step/tie-break PBE form and bundled unique-PBE outcome- and utility-equality endpoints,
  plus finite completed-rank slot/payment and utility endpoints with matching
  unique-PBE packages. It also exposes ordered-assumption completed-rank
  paper-formula endpoints and unique-PBE wrappers for slot assignment, finite
  `B*` threshold payment, VCG-tail accounting, and the `[0, value]` payment
  interval, including threshold-reached variants. The schedule-level wrapper
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`
  now generates the no-overshoot terminal history and exact terminal records
  directly from sorted no-duplicate finite `B*` schedule data. The strict
  ordered cold-start wrapper further reduces that schedule check to adjacent
  threshold sortedness plus the last-threshold unscheduled comparison.
- A source-extensive terminal-record checker,
  `paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game`,
  now strengthens the finite schedule route by putting the concrete generated
  history and terminality proof inside the PBE predicate. Its sorted schedule
  endpoint and strict ordered cold-start threshold-sorted endpoint return
  unique PBE plus the displayed completed-rank paper formulas from the same
  finite schedule data, with all-scheduled paper-interface wrappers that set
  the completed rank set to the schedule `toFinset` automatically and
  singleton/pair shortcuts for small cold-start schedule checks. Companion
  singleton/pair record-audit wrappers expose the exact terminal dropout
  records and active-rank characterizations. The source-extensive PBE trace
  wrapper, now also exposed from the reusable auction layer, returns the exact
  finite-`B*` dropout-history certificate. The sorted-schedule trace endpoint
  `theorem8_terminal_record_source_extensive_schedule_trace_completed_conclusion`
  and its all-scheduled wrapper now bundle the unique PBE, named finite `B*`
  strategy, generated history, terminality, exact finite `B*` dropout history,
  and completed-rank formulas directly from schedule data. The cold-start
  threshold-sorted trace endpoint and singleton/pair trace shortcuts expose the
  same package with paper-native finite-schedule premises. The all-terminal
  source-extensive endpoints give unique PBE with VCG outcome, rankwise
  slot/payment, bidder utility equality, and a bundled all-terminal VCG
  conclusion when no active ranks remain. The
  generic no-overshoot record audit exposes exact terminal dropout records for
  any inactive rank in a no-overshoot terminal certificate. The generic
  no-overshoot endpoint also has a
  threshold-reached variant that derives completed-rank inactivity from the
  terminal clock cutoff. `PaperInterface.lean` exposes these as the current
  preferred finite paper-checking forms and includes a one-stop trace endpoint
  bundling unique PBE, named strategy, generated history, terminality, and the
  completed-rank formulas.
  The source-extensive rationality predicate is now also split into local
  deviation, generated history, and terminality by
  `paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_iff_local_deviation_history_terminal`;
  the terminal-record checker exposes the same split as a direct PBE iff and,
  for audited no-overshoot terminal certificates, a PBE iff with local deviation
  alone plus an equivalent one-step/tie-break form.
- A formal overshoot witness,
  `paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_record`,
  shows that bare strategy-consistent histories can be terminal but still
  record a dropout one unit above the exact finite `B*` threshold. This records
  the proof-strategy constraint that exact terminal-record source theorems need
  exact-drop or no-overshoot timing evidence. The paper interface now exposes
  the ordinary-history bridge
  `theorem8_strategy_history_to_exact_drop_history_of_no_overshoot_drop_steps`,
  which converts a named-strategy history plus no-overshoot dropout-step
  evidence into an exact finite `B*` history. A new clock-disciplined
  source-transition history proves that exact records follow when clock
  advances never pass active finite `B*` thresholds, also forgets to the
  ordinary generated named-strategy history, bundles those two obligations for
  source-proof callers, packages terminal disciplined histories into
  no-overshoot terminal certificates, exposes a direct
  source-extensive completed-threshold endpoint for those terminal histories
  plus a trace-refined version that also returns the named finite `B*`
  strategy, generated history, terminality, and exact finite `B*` dropout trace.
  The paper interface now has both terminal-clock and direct completed-rank
  inactivity trace forms for clock-disciplined source-extensive histories,
  with belief-explicit paper-interface forms
  `theorem8_clock_disciplined_terminal_history_belief_source_extensive_completed_threshold_conclusion`
  and
  `theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion`,
  direct all-terminal clock-disciplined VCG outcome, slot/payment, utility, and
  bundled VCG endpoints, plus cold-start all-terminal wrappers that derive the
  initial no-overshoot and activity premises from the paper cold-start state
  while preserving the source-extensive or belief-explicit trace,
  and a finite-schedule bridge shows clock-sorted no-duplicate
  schedules induce that disciplined history under the
  active-unscheduled-threshold premise, with singleton and pair shortcuts for
  small schedule checks. A lighter finite-schedule ledger now returns the
  generated named-strategy history and exact records directly from a
  clock-sorted no-duplicate schedule. The paper interface also proves that a
  finite cold-start schedule over the current `ℕ`-rank state leaves an
  unscheduled rank active, so finite checks should target completed-rank
  endpoints unless a finite-bidder source model is added.
- The finite schedule route now has a direct source-shaped endpoint:
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_clock_sorted_nodup`.
  It starts from the source-shaped core certificate plus sorted schedule data
  and returns unique PBE with completed-rank terminal-record formulas.
  A one-stop variant,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_source_sequential_rationality_core_source_completion_of_source_iff_clock_sorted_nodup`,
  constructs that source-shaped core certificate internally from concrete
  belief consistency and the game-level source sequential-rationality iff.
  The ex-post local-deviation all-scheduled paper-interface endpoint exposes
  the same finite terminal-record conclusion when the sharper source
  certificate is available. A cold-start threshold-sorted paper-interface
  wrapper constructs that source certificate internally from the local-deviation
  model and schedule data.
- `PaperInterface.lean` now also exposes the finite ex-post source boundary:
  sequential rationality iff local deviation, one-step best response implying
  named-strategy sequential rationality for every belief, and the belief-free
  named-strategy local-deviation discharge.
- The paper interface also exposes the no-overshoot terminal-history ex-post
  source-completion route: PBE iff named finite `B*` strategy, a
  threshold-reached completed-rank unique-PBE terminal-record conclusion, the
  matching completed-rank utility equality, and the all-rank ordered
  terminal-record conclusion under all-rank terminal inactivity.
- Direct local-deviation source-completion consequences now expose named-strategy
  PBE, arbitrary-PBE strategy equality, unique PBE, and arbitrary-PBE VCG
  outcome equality without requiring reviewers to manually compose intermediate
  certificates.
- A source-shaped local-deviation dynamic game now makes consistency trivial
  and sequential rationality exactly the local-deviation theorem target. It has
  direct constructed-outcome, strict ordered terminal-dynamic, core
  source-completion, and unique-PBE-with-full-conclusion endpoints, so the
  remaining extensive-form work can target the local-deviation characterization
  and exact terminal records directly.
  It also exposes
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_pbe_iff_named_strategy`,
  the plain behavioral PBE iff named-strategy characterization at this boundary.
  The full-conclusion endpoint also has a sorted exact-drop schedule
  specialization,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt`,
  which lets reviewers check the local-deviation route directly from schedule
  facts.
- The finite exact-schedule core source-completion constructor now has a
  local-deviation specialization:
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_core_source_completion_certificate_of_local_deviation_dynamic_clock_sorted_nodup_unscheduled_threshold_gt`.
  This composes the sorted exact-drop schedule obligation with the
  source-shaped local-deviation dynamic game.
  The same schedule hypotheses now also feed the direct unique-PBE
  terminal-record endpoint
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_core_source_completion_exists_unique_pbe_of_local_deviation_dynamic_clock_sorted_nodup_unscheduled_threshold_gt`,
  so reviewers can check the finite source-completion conclusion from one
  declaration rather than manually composing the certificate constructor.
  The all-scheduled variant
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_core_source_completion_exists_unique_pbe_of_local_deviation_dynamic_clock_sorted_nodup_unscheduled_threshold_gt`
  removes the completed-rank inclusion premise when the verified finite ranks
  are exactly `scheduledRanks.toFinset`.
  For nonempty schedules written as `scheduledPrefix ++ [lastRank]`,
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_clock_append_singleton`
  proves that the final clock equals the last scheduled finite `B*` threshold,
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_clock_sorted_nodup_last_threshold_lt_unscheduled`
  exposes the same last-threshold terminality simplification for the full
  terminal/dynamic/ordered-outcome conclusion, with cold-start specialization
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_cold_start_clock_sorted_nodup_last_threshold_lt_unscheduled`
  discharging initial activity from the canonical no-dropout state. For a
  singleton cold-start schedule,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_cold_start_singleton_last_threshold_lt_unscheduled`
  also discharges sortedness and no-duplication; the two-rank endpoint
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_cold_start_pair_last_threshold_lt_unscheduled`
  reduces schedule verification to adjacent threshold order, rank inequality,
  and unscheduled-threshold comparisons. The finite terminal-record endpoint
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_core_source_completion_exists_unique_pbe_of_local_deviation_dynamic_clock_sorted_nodup_last_threshold_lt_unscheduled`
  uses that fact to replace the recursive final-state terminality premise with
  a last-threshold comparison for every unscheduled rank; its cold-start
  specialization
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_core_source_completion_exists_unique_pbe_of_local_deviation_cold_start_clock_sorted_nodup_last_threshold_lt_unscheduled`
  also removes the explicit initial-activity premise; the singleton endpoint
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_singleton_core_source_completion_exists_unique_pbe_of_local_deviation_cold_start_last_threshold_lt_unscheduled`
  removes sortedness and no-duplication too, while
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_pair_core_source_completion_exists_unique_pbe_of_local_deviation_cold_start_last_threshold_lt_unscheduled`
  provides the analogous two-rank terminal-record route.
  General finite lists can now use
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted`
  plus
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_of_threshold_sorted`
  to replace recursive clock-sortedness with adjacent threshold-order checks.
  The nil, singleton, cons-cons, and pair helpers for
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted`
  make concrete finite schedules auditable by local inequalities.
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted_append_singleton`
  supports incremental schedule construction from a previously sorted prefix
  plus the single boundary check
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_last_threshold_le`,
  whose nil, singleton, and cons-cons helpers expose the local boundary check.
  The corresponding cold-start source endpoints are
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_core_source_completion_exists_unique_pbe_of_local_deviation_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`.
  The same route now exposes reusable certificate constructors,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_behavior_certificate_of_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_certificate_of_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_core_source_completion_certificate_of_local_deviation_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`,
  so source audits can inspect the constructed terminal-history,
  terminal-dynamic, and source-completion objects before applying the final
  unique-PBE theorems.
  The same cold-start threshold-sorted finite-schedule route now has the
  explicitly named terminal-record endpoint
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_core_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_local_deviation_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled`.
  Singleton and pair cold-start routes also have explicitly named
  terminal-history behavior certificates, direct certificate-level exact-record
  and active-status facts, and `with_terminal_record_conclusion` aliases.
  Exact schedule record generation is also exposed at the deterministic final
  state by
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_terminal_record_eq_threshold_of_mem_of_clock_sorted_nodup`
  and
  `paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_active_iff_not_mem_of_clock_sorted_nodup`,
  with cold-start threshold-sorted local-deviation specializations
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_threshold_sorted_final_state_terminal_record_eq_threshold_of_mem`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_threshold_sorted_final_state_active_iff_not_mem`.
  The cold-start threshold-sorted terminal-history certificate itself now also
  exposes these facts directly through
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_final_state_terminal_record_eq_threshold_of_mem`
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_final_state_active_iff_not_mem`.
  The strict ordered exact-history terminal-dynamic certificate also exposes
  the direct outcome equality
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_history_terminal_record_outcome_eq_bstar`,
  so reviewers can check the terminal-record outcome against the constructed
  successor-tail ranked `B*` outcome before reading componentwise conclusions.
  The same exact-history terminal-dynamic boundary now has a direct
  unique-PBE endpoint bundling that terminal-record outcome equality. The
  all-rank ex-post local-deviation exact-history source-completion certificate
  packages the belief-independent local-deviation source semantics together
  with exact terminal-record generation into one final source-boundary object.
  The finite exact-history analogue packages the same ex-post local-deviation
  source semantics with exact terminal records and inactive-on-completed
  evidence for a finite completed rank set, then derives the existing
  unique-PBE terminal-record conclusion for that finite paper instance.
  Direct local-deviation exact-history and exact-schedule constructors now
  instantiate that finite ex-post source object, with an all-scheduled variant
  discharging the completed-subset premise. A direct sorted finite-schedule
  endpoint also starts from the ex-post local-deviation certificate and derives
  the finite terminal-record unique-PBE conclusion without requiring reviewers
  to manually convert through the ex-post one-sided Step 1/Step 2 layer; its
  all-scheduled variant removes the completed-subset proof when the completed
  ranks are `scheduledRanks.toFinset`. The cold-start threshold-sorted finite
  schedule route now has a direct ex-post local-deviation certificate and
  unique-PBE terminal-record endpoint, so the main finite schedule audit no
  longer needs to pass through the core source certificate manually. Singleton
  and pair cold-start ex-post helpers reduce small concrete schedules to the
  rank-local unscheduled-threshold and adjacent-threshold checks. The all-rank
  and finite exact-history ex-post source objects now also expose direct
  obligation ledgers spelling out belief consistency, belief-independent
  one-step-to-sequential-rationality, the local-deviation iff, exact history,
  and terminal inactivity evidence. The dropout-price formula also now has
  scalar and ranked continuity-in-valuation lemmas matching the Theorem 8
  continuity restriction. The exact-history terminal-record route now also
  exposes direct utility equality with the constructed successor-tail ranked
  `B*` outcome, making the paper's "same position and payoff" wording
  directly auditable from outcome equality; the finite exact-history route has
  the same utility-equality endpoint on every completed rank. The paper's
  empty-history convention `b_{k+1} = 0` is now exposed as scalar and ranked
  dropout-price formulas. Strict adjacent click-through rates now also give
  scalar and ranked injectivity of the dropout price in valuation, a direct
  uniqueness-facing strengthening of the existing strict monotonicity. The same
  facts are exposed through source proof-line `q` aliases for continuity,
  empty history, injectivity, affine form, interval/bound facts, and history
  monotonicity. The abstract dynamic-game interface now has a
  direct utility-equals-VCG bridge from same-slot/same-payment fields and from
  full outcome equality. The ex-post local-deviation source boundary now also
  exposes the belief-independent named-strategy sequential-rationality endpoint
  and the arbitrary-strategy sequential-rationality iff local-deviation
  characterization directly, with lifts to the final all-rank and finite
  exact-history source objects for direct audit citations. It also exposes the
  direct named-strategy local-deviation discharge from the one-step
  best-response obligation at those same source layers, in both explicit-belief
  and nonempty-belief citation forms, together with named-strategy "for all
  beliefs" iff local-deviation endpoints.
  The source-obligation audit surface now also exposes the minimized core
  conjunction
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_core_source_completion_obligations`
  and the sharper local-deviation conjunction
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_core_source_completion_obligations`,
  and the reduced source-completion layers now also expose direct
  `exists_unique_pbe_with_conclusion` endpoints. These let a reviewer cite
  core, one-step/tie-break, sequential-rationality, local-deviation, one-sided,
  or ex-post certificates and immediately obtain the compact unique-PBE
  terminal-dynamic paper conclusion without manually composing conversion
  lemmas. The obligation-conjunction declarations separate the human checks for
  consistency, source sequential rationality, PBE behavior, and the
  local-deviation characterization. The intermediate layers are also exposed by
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_core_source_completion_obligations`,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_obligations`,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_sequential_rationality_core_source_completion_obligations`,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_one_sided_source_completion_obligations`,
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_one_sided_source_completion_obligations`.
  The new ex-post local-deviation certificate converts both to the
  local-deviation core route and to the ex-post one-sided Step 1/Step 2 route,
  matching the paper's belief-independent best-response wording; the strict
  ordered local-deviation dynamic-game checker now instantiates this ex-post
  local-deviation boundary directly. It also has concrete checker endpoints
  that apply the already-proved strict one-step best-response theorem
  internally, giving named-strategy sequential rationality for every belief and
  the named local-deviation predicate without passing a separate best-response
  proof. With a no-overshoot terminal history, the same checker now also
  reuses the named-strategy history as the generated history for any PBE
  strategy, derives the exact finite `B*` dropout history, and proves the
  completed-rank terminal-record paper formulas directly from that history,
  including a threshold-reached variant that derives completed-rank inactivity
  from the final clock cutoff and a unique-PBE bundle with those displayed
  formulas. `PaperInterface.lean` exposes the PBE-iff checkpoint as
  `theorem8_ex_post_no_overshoot_terminal_history_source_completion_pbe_iff_named_strategy`.
  Under all-rank terminal inactivity it also gives the all-rank
  ordered terminal-record paper conclusion and a matching unique-PBE bundle,
  now exposed directly in `PaperInterface.lean` as
  `theorem8_ex_post_no_overshoot_terminal_history_source_completion_ordered_terminal_record_conclusion`,
  removing a separate all-PBE history-generation premise for this checker. The ex-post
  local-deviation layer also exposes direct downstream
  cutoff, paper-conclusion, and
  unique-PBE-with-conclusion endpoints.
  The source-shaped no-overshoot terminal-dynamic route now also exposes
  completed-rank utility equality between terminal dropout records and the
  constructed successor-tail `B*` outcome from the same finite completed-rank
  data.
  One-step/tie-break, sequential-rationality, one-sided, and ex-post
  certificates now also have direct named-strategy PBE, PBE strategy-equality,
  PBE cutoff-rule, unique-PBE, and PBE-to-VCG outcome endpoints, avoiding
  manual conversion through the core certificate in the paper audit file.
  The full, core, and local-deviation certificates likewise expose direct
  `pbe_drops_iff_threshold_bid` endpoints for the main paper-facing cutoff rule,
  plus named Step 1/Step 2 corollaries for dropping at or after the threshold
  and not dropping before it. The one-step/tie-break, sequential-rationality,
  one-sided, and ex-post routes expose the same Step 1/Step 2 corollaries.
  Core, one-step/tie-break, sequential-rationality, local-deviation,
  one-sided, and ex-post source certificates now also have direct compact
  paper-conclusion endpoints.
  Cold-start sortedness helpers
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_cold_start_clock_le_local_deviation_exact_schedule_price`,
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_singleton`,
  and
  `paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_pair`
  discharge the initial clock inequality automatically for singleton and pair
  exact schedules.
- The core source-completion boundary now has the same one-step/tie-break
  split: the existing core certificate follows from belief consistency,
  one-step-to-sequential-rationality, PBE one-step best response, and PBE
  threshold tie-breaking.
- The strict ordered core source-completion boundary also has the same
  sequential-rationality split:
  `PaperTheorem8BStarRankedThresholdStrictOrderedSequentialRationalityCoreSourceCompletionCertificate`
  derives the one-step/tie-break core certificate, the existing core
  source-completion certificate, the one-sided Step 1/Step 2 certificate, and
  the full source-completion certificate.
- The same split also recovers the paper's one-sided Step 1/Step 2 certificate,
  so the source proof can be audited in either cutoff-iff form or one-sided
  exclusion form, and it now derives the full source-completion certificate as
  well.
- Theorem 8 also has bundled exact and strict paper-facing PBE conclusion, including cutoff-complement
  endpoints and named-equilibrium conclusion endpoints, including cutoff-complement variants, constructed
  ranked `B*` outcome formulas, and constructed-outcome certificate bridges, so a human reviewer can
  inspect one audit theorem rather than reconstruct the result from component
  lemmas.
- Theorem 8 has a reduced-form dynamic-game scaffold whose PBE predicate
  recognizes exactly the named finite `B*` strategy and whose outcome map is
  definitionally the constructed ranked `B*` outcome and VCG-equivalent by
  construction. The scaffold includes constructed-outcome certificate wrappers, direct ordered VCG/named-strategy
  outcome-quality audit wrappers plus one-stop ordered and strict-ordered reduced-form audit wrappers plus a general strict constructed-certificate ordered named-strategy audit wrapper, a cold-start formal-terminal witness and closed cold-start reduced-form unique-PBE/full-conclusion audit wrapper, and direct exact/strict named-strategy conclusion audit wrappers. The cold-start witness is quiescent rather than a source auction-completion history. This validates the certificate
  interface end-to-end, but it is not the source generalized-English
  extensive-form proof.
- Theorem 8 now has terminal dropout-record outcome bridges: exact terminal
  records imply the constructed ranked `B*` outcome, and exact-drop histories
  give rank-local and finite-prefix finite `B*` payment, VCG-tail accounting,
  and `[0, value]` payment bounds, plus an ordered all-ranks terminal-record
  paper conclusion when all ranks complete. The strict ordered terminal-dynamic
  certificate can now be augmented with concrete exact-history completion to
  give both compact PBE behavior and the terminal-record ordered outcome
  conclusion, with a finite completed-rank variant for paper instances.
- Theorem 8 now has a single-step exact finite-`B*` source-history constructor:
  if the clock can advance to an active rank's threshold, advancing there and
  recording the dropout is an exact-drop history and the terminal record is
  exactly that threshold. Exact histories compose, and an append-single wrapper
  gives the basic finite-schedule construction step. A list-based exact-drop
  schedule predicate now converts finite ordered schedules into exact histories,
  terminal records, final inactivity for scheduled ranks, final activity for
  unscheduled initially active ranks, finite terminal-record outcome
  conclusions, direct named-strategy reachability histories, and finite
  terminal-dynamic/source-completion endpoints. A
  sorted-threshold/no-duplicate constructor now builds such a schedule from a
  clock-sorted initially active rank list, and a sorted finite-schedule
  source-completion wrapper feeds that constructor directly into the unique-PBE
  terminal-record endpoint. The sorted finite-schedule wrapper now also has a
  core source-completion form, so the strongest finite endpoint takes only the
  three core PBE obligations plus the exact schedule.
- Theorem 8 finite schedule verification is now more directly human-checkable:
  clock-sorted schedule premises have `nil`, `cons_iff`, `singleton`, and
  `pair` helpers; deterministic final clocks have empty/nonempty/singleton/pair
  helpers; exact schedules build terminal-history behavior certificates from
  the rank-local check that unscheduled thresholds exceed the final clock; and
  strict ordered dynamic certificates plus sorted schedule data assemble the
  integrated terminal-dynamic and finite-schedule core source-completion
  certificates, with direct unique-PBE terminal-record and trace-refined
  endpoints from the same inputs. The continuation-threshold bridge
  `paper_theorem8_bstar_continuation_threshold_le_current_threshold_of_ordered_tail`
  is now formalized; same-tail adjacent threshold order remains an explicit
  schedule-sortedness premise, which is the right boundary for finite schedules
  rather than an ordered-values corollary. The two-rank
  `pair_or_swap` helpers show that a displayed pair or its swap is always
  sorted, so small paper checks can choose by threshold order instead of rank
  convention.
  The trace-refined endpoint carries the named finite `B*` strategy, full
  terminal/dynamic/ordered-outcome conclusion, generated history, terminality,
  and exact finite `B*` dropout trace. A cold-start threshold-sorted wrapper
  now gives that trace-full source-shaped endpoint without a separate
  clock-sorted proof obligation, and a schedule-free clock-disciplined terminal
  history wrapper gives the same trace-full source-shaped conclusion directly
  from any disciplined terminal history, with a completed-rank variant that
  adds terminal-record payment, VCG-tail, and payment-bound formulas from the
  same history. A generic no-overshoot terminal/dynamic wrapper provides the
  corresponding lower-level composition form. The concrete local-deviation
  checker now also has a no-overshoot terminal/dynamic trace-full endpoint
  that includes unique PBE, named strategy identity, generated history,
  terminality, exact records, and completed-rank formulas from final-clock
  threshold premises.
- Theorem 8 now also has a finite exact-history source-completion endpoint:
  once the concrete source proof supplies belief consistency, sequential
  rationality, behavioral PBE characterization, and exact completion of the
  finite rank set, Lean derives unique PBE plus compact terminal/dynamic/VCG
  behavior and terminal-record payment/VCG-tail conclusions for those ranks.
  A core source-completion layer now proves arbitrary-PBE VCG slot/payment
  equality from behavioral uniqueness plus constructed-outcome agreement, so
  slot/payment equality is not a separate source-PBE obligation.

## Remaining obligations

- Theorem 7: the strongest revenue-minimality theorem still keeps the
  comparison-outcome no-positive-transfers/no-subsidy premise explicit.
- Theorem 8: concrete belief consistency and the game-level iff between
  `isSequentiallyRational` and the source-shaped reachable/off-path predicate
  for the real generalized-English game are now the main source-semantics
  obligations. The direct source-iff wrappers then provide the full conclusion
  when generated PBE histories, no-overshoot timing, and outcome/VCG
  identifications are supplied, and the no-overshoot terminal/dynamic wrappers
  use the same source iff when those history facts are already packaged.
  Clock-disciplined terminal histories and finite sorted schedules now have
  trace-full endpoints with exact finite `B*` dropout histories and
  completed-rank terminal-record formulas. Bare arbitrary strategy histories
  remain too weak: the formal overshoot witness shows why a no-overshoot,
  exact-drop, schedule, or clock-discipline premise is needed for terminal
  record generation.

## Commands run

```bash
lake build EOS07GSP
lake build
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
python3 scripts/check_smoke.py
python3 scripts/audit_repository.py
```

The Lean builds completed successfully during this audit pass. The latest full
`lake build` completed successfully with 3564 jobs. The smoke check completed
successfully when invoked through `python3`; direct script execution is not
enabled in this checkout. The DAG render command was run earlier for the
current audit artifacts.
The 2026-05-06 pass reran `lake build EOS07GSP`, full `lake build`, and
`python3 scripts/check_smoke.py` after adding the one-step/off-threshold
best-response, one-step dynamic sequential-rationality bridge, and direct
one-step dynamic PBE endpoint layers. The same checks were rerun after adding
the one-step/tie-break behavioral and source-completion certificate splits, and
again after adding the generic off-threshold-plus-tie cutoff assembly theorems.
They were rerun after adding the sequential-rationality-to-one-step/tie-break
source-completion bridge and the reduced-form instantiation of that narrowed
certificate, and again after adding the local-deviation sequential-rationality
certificate, its strict ordered source-completion bridges, and the reduced-form
strict ordered local-deviation source-completion instantiation.
They were rerun after adding the source-shaped reachable/off-path
sequential-rationality predicate, its equivalence with the local-deviation
target, named/strict/strict-ordered wrappers, and paper-audit aliases.
They were rerun again after adding the strict ordered source-shaped
source-completion certificate bridge and its audit aliases.
They were rerun again after adding the source-shaped dynamic checker, its PBE
iff endpoints, its local-deviation dynamic certificate, and audit aliases.
They were rerun again after adding the sorted finite-schedule endpoint for the
source-shaped core source-completion route and its audit alias.
They were rerun again after adding the one-stop sorted finite-schedule
source-shaped route from concrete belief consistency and the game-level source
sequential-rationality iff.
They were rerun again after adding the strict ordered source-shaped
constructed-outcome certificate and direct sorted-schedule full-conclusion
endpoints, including the no-overshoot variant.
They were rerun again after adding direct source-shaped core source-completion
PBE behavior endpoints and paper-audit aliases.
The rendered DAG PDF was rasterized to a PNG and visually inspected after
shortening the Theorem 8 node label.
The 2026-05-15 pass reran `lake build EOS07GSP` after adding direct
no-overshoot terminal-dynamic/source-completion endpoints, paper-audit aliases,
and completed-rank payoff-equality wrappers for no-overshoot terminal
histories. The same pass added and rebuilt a nonempty-schedule no-overshoot
terminal-dynamic endpoint whose unscheduled-rank premise uses the last
scheduled threshold. A follow-up pass added no-overshoot cold-start
terminal-dynamic endpoints for threshold-sorted nonempty schedules and for
singleton/pair schedules, exposed them in `PostPaperAudit.lean`, and rebuilt
`lake build EOS07GSP` successfully with 2908 jobs. The same follow-up added
direct PBE utility-equals-VCG theorems for the core and full source-completion
boundaries, an all-PBE utility-equals-VCG theorem for the concrete no-overshoot
source-history route, and exposed the audit aliases. A later pass added the
local-deviation core no-overshoot source-history endpoint family and a
source-shaped all-PBE slot/payment, outcome-equals-VCG, and utility-equals-VCG
wrapper family for generated histories. The same pass added local-deviation
and source-shaped constructors from generated no-overshoot histories to the
full source-completion certificate and one-stop unique-PBE/full-conclusion
endpoints for those history routes. A follow-up added the preferred
no-overshoot terminal-dynamic source-shaped endpoint, which consumes the
annotated finite history directly instead of requiring a global no-overshoot
predicate over all states. Another follow-up added the finite completed-rank
variant, which only requires terminal inactivity on the completed finite rank
set and returns unique PBE plus terminal-record slot/payment/VCG-tail formulas.
It was rebuilt with `lake build EOS07GSP`.
A later pass added the
terminal-record local-deviation dynamic game: its `outcomeOf` is the terminal
dropout-record outcome, and its exact/no-overshoot history endpoints prove
unique PBE with outcome equality and direct bidder utility equality to the
successor-tail ranked `B*`/VCG target under the all-inactive terminal-state
premise. The same surface now exposes finite completed-rank slot/payment and
utility equality, including exact and no-overshoot threshold-reached variants
that derive completed-rank inactivity from the terminal clock threshold check.
It also has a cold-start threshold-sorted schedule endpoint that maps a
displayed nonempty no-duplicate schedule directly to completed-rank
slot/payment and utility equality for any PBE in the terminal-record game.
Singleton and pair forms now expose the same terminal-record game conclusions
from the smaller local premises used in small displayed paper examples.
The terminal-record game also has finite completed-rank unique-PBE packages
for exact, no-overshoot, threshold-reached, and cold-start threshold-sorted
routes, including singleton and pair specializations, bundling equilibrium
uniqueness with the finite slot/payment and utility conclusions.
Exact and no-overshoot completed-rank paper-conclusion endpoints now expose the
displayed slot, threshold-payment, VCG-tail, and payment-interval formulas
directly for terminal-record game PBEs under ordered assumptions, with matching
unique-PBE wrappers for the equilibrium statement itself.
The cold-start threshold-sorted terminal-record game route now has matching
displayed-formula and unique-PBE displayed-formula wrappers, including
singleton and pair forms for small displayed schedules.
The 2026-05-16 pass reran `lake build EOS07GSP` after adding the direct
source-iff full-conclusion endpoint, the no-overshoot terminal/dynamic
source-iff full and completed-rank wrappers, the clock-disciplined
source-iff full and completed-rank wrappers, and the belief-explicit
source-extensive clock-disciplined completed-rank wrappers. Each pass compiled
before its scoped commit was pushed.
The same pass then rebuilt `lake build EOS07GSP` after adding the terminal-local
strict ordered upgrade and the source-sequential no-overshoot terminal-history
full-conclusion wrapper that no longer asks for a separate model-equality proof.
It was rerun again after extending that terminal-local route to the
trace-refined completed-rank source-shaped endpoint.
It was rerun again after adding the cold-start clock-disciplined
source-shaped trace endpoint, which derives the initial no-overshoot timing
premise from the cold-start clock and nonnegative finite `B*` thresholds.
The same pass added the source-extensive cold-start clock-disciplined wrapper,
so generated history and terminality can remain inside the PBE checker without
restating the cold-start initial-timing facts.
It was rerun again after adding the canonical belief witness for the
belief-explicit source-extensive checker, including explicit consistency,
sequential-rationality, and named-strategy PBE witness wrappers.
It was rerun again after adding the cold-start belief-explicit
clock-disciplined wrapper, which keeps the generated-history and terminality
evidence in the belief object while deriving the cold-start timing premises.
It was rerun again after adding the cold-start all-terminal source-extensive
and belief-explicit clock-disciplined trace wrappers, which bundle unique PBE,
named-strategy identity, generated history, terminality, exact finite `B*`
records, and VCG outcome/slot-payment/utility conclusions from the paper
cold-start state.
It was rerun again after adding the finite cold-start schedule guardrail theorem
showing that, in the current `ℕ`-rank cold-start model, any finite schedule
leaves an unscheduled rank active.
It was rerun again after adding direct completed-rank inactivity trace wrappers
for no-overshoot, clock-disciplined, and cold-start clock-disciplined
source-extensive histories, and again after adding the matching belief-explicit
direct-inactivity trace wrappers.
`python3 scripts/audit_repository.py` still reports unrelated root/status-table
issues outside EOS07GSP: unexpected root statuses for
`papers/DSWG24DiscretizationBias` and `papers/GS62CollegeAdmissions`, a missing
root status row for `IM05MarriageHonestyStability`, and warnings in GS62, IM05,
and Roth README status rows.

## Cross-check summary

- `PostPaperAudit.lean` imports and compiles from the paper root.
- `README.md`, `POST_PAPER_AUDIT_REPORT.md`, the project `README.md`, and
  `docs/ECONCSLEAN_CURRENT_STATUS.md` record the same conditional boundary.
- `DependencyDAG.tex` was rendered after the Theorem 7 and Theorem 8 node
  updates.
