import EconCSLib.MechanismDesign.Auctions.MainTheorems

/-!
# EOS Theorem 8 Source Bridges

This module holds late-stage source-proof bridges for EOS Theorem 8.  It
imports the large auction theorem surface, but keeping new conditional source
endpoints here lets future proof iterations avoid rebuilding the monolithic
`MainTheorems.lean` file when only these bridge statements change.
-/

namespace EconCSLib
namespace Auction

/--
The core source-completion certificate already contains enough information to
recover the local one-step/tie-break certificate. PBE cutoff behavior gives
PBE strategy equality with the named finite `B*` strategy, so the named
strategy's one-step optimality and threshold tie-breaking supply the local
fields.
-/
def paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_certificate_of_core
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedCoreSourceCompletionCertificate
        Belief) :
    PaperTheorem8BStarRankedThresholdStrictOrderedOneStepTieBreakCoreSourceCompletionCertificate
      Belief where
  integrated := cert.integrated
  concrete_belief_consistency := cert.concrete_belief_consistency
  one_step_best_response_implies_sequential_rationality := by
    intro _hbest
    exact cert.concrete_sequential_rationality
  pbe_one_step_best_response := by
    intro strategy hpbe
    have hstrategy :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_core_source_completion_pbe_strategy_eq_named
        cert hpbe
    rw [hstrategy]
    exact
      paper_theorem8_bstar_ranked_threshold_strict_named_strategy_one_step_best_response
        cert.integrated.dynamic.base.strictModel
  pbe_drop_at_threshold := by
    intro strategy hpbe
    have hstrategy :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_core_source_completion_pbe_strategy_eq_named
        cert hpbe
    rw [hstrategy]
    exact
      paper_theorem8_bstar_ranked_threshold_strict_named_strategy_drop_at_threshold
        cert.integrated.dynamic.base.strictModel

/--
The full source-completion certificate forgets to the local one-step/tie-break
core certificate by discarding the already-derived VCG slot/payment fields.
-/
def paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_certificate_of_source_completion
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedSourceCompletionCertificate
        Belief) :
    PaperTheorem8BStarRankedThresholdStrictOrderedOneStepTieBreakCoreSourceCompletionCertificate
      Belief :=
  paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_certificate_of_core
    { integrated := cert.integrated
      concrete_belief_consistency := cert.concrete_belief_consistency
      concrete_sequential_rationality := cert.concrete_sequential_rationality
      concrete_pbe_behavior := cert.concrete_pbe_behavior }

/--
The paper's one-sided Step 1/Step 2 source-completion certificate can also be
read as a one-step/tie-break core source-completion certificate.  Step 1/Step 2
already imply every PBE strategy is extensionally the named finite `B*`
strategy; the named strategy's one-step optimality and threshold tie-breaking
then supply the local behavioral fields.
-/
def paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_certificate_of_one_sided
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedOneSidedSourceCompletionCertificate
        Belief) :
    PaperTheorem8BStarRankedThresholdStrictOrderedOneStepTieBreakCoreSourceCompletionCertificate
      Belief where
  integrated := cert.integrated
  concrete_belief_consistency := cert.concrete_belief_consistency
  one_step_best_response_implies_sequential_rationality := by
    intro _hbest
    exact cert.concrete_sequential_rationality
  pbe_one_step_best_response := by
    intro strategy hpbe
    have hstrategy :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_one_sided_source_completion_pbe_strategy_eq_named
        cert hpbe
    rw [hstrategy]
    exact
      paper_theorem8_bstar_ranked_threshold_strict_named_strategy_one_step_best_response
        cert.integrated.dynamic.base.strictModel
  pbe_drop_at_threshold := by
    intro strategy hpbe
    have hstrategy :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_one_sided_source_completion_pbe_strategy_eq_named
        cert hpbe
    rw [hstrategy]
    exact
      paper_theorem8_bstar_ranked_threshold_strict_named_strategy_drop_at_threshold
        cert.integrated.dynamic.base.strictModel

/--
Ex-post one-sided source completion also packages as the one-step/tie-break
core source certificate, by first forgetting the ex-post rationality field to
the belief-specific one-sided certificate.
-/
def paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_certificate_of_ex_post_one_sided
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostOneSidedSourceCompletionCertificate
        Belief) :
    PaperTheorem8BStarRankedThresholdStrictOrderedOneStepTieBreakCoreSourceCompletionCertificate
      Belief :=
  paper_theorem8_bstar_ranked_threshold_strict_ordered_one_step_tie_break_core_source_completion_certificate_of_one_sided
    (paper_theorem8_bstar_ranked_threshold_strict_ordered_one_sided_source_completion_certificate_of_ex_post
      cert)

/--
An ordinary named-strategy step that satisfies the active-rank advance-safety
bound preserves the active-rank no-overshoot invariant.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_step_preserves_state_no_overshoot_of_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state next)
    (hadvance_safe :
      ∀ newPrice,
        next =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            state newPrice →
          ∀ rank,
            state.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∀ rank,
      next.IsActive rank →
        next.clockPrice ≤
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_preserves_state_no_overshoot
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_step_to_clock_disciplined_strategy_step_of_advance_safe
        model hstep hadvance_safe)
      hstate_no_overshoot

/--
At a realized new dropout of an advance-safe ordinary named-strategy step, the
pre-dropout clock has not overshot the dropping rank's finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_step_realized_new_dropout_no_overshoot_of_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state next)
    (hadvance_safe :
      ∀ newPrice,
        next =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            state newPrice →
          ∀ rank,
            state.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hactive : state.IsActive rank)
    (hinactive : ¬ next.IsActive rank) :
    state.clockPrice ≤
      paper_theorem8_bstar_threshold_bid
        model.value model.clickThroughRate (model.remaining + 1)
        (rank + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_realized_new_dropout_no_overshoot
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_step_to_clock_disciplined_strategy_step_of_advance_safe
        model hstep hadvance_safe)
      hstate_no_overshoot hactive hinactive

/--
At a realized new dropout of an advance-safe ordinary named-strategy step, the
new dropout record is exactly the dropping rank's finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_step_new_dropout_record_eq_threshold_of_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state next)
    (hadvance_safe :
      ∀ newPrice,
        next =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            state newPrice →
          ∀ rank,
            state.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hactive : state.IsActive rank)
    (hinactive : ¬ next.IsActive rank) :
    next.lastDropout rank =
      some
        (paper_theorem8_bstar_threshold_bid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_new_dropout_record_eq_threshold
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_step_to_clock_disciplined_strategy_step_of_advance_safe
        model hstep hadvance_safe)
      hstate_no_overshoot hactive hinactive

/--
An ordinary named-strategy history whose clock advances are active-rank safe
preserves the active-rank no-overshoot invariant through the final state.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_preserves_state_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∀ rank,
      finalState.IsActive rank →
        finalState.clockPrice ≤
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_preserves_state_no_overshoot
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe)
      hstate_no_overshoot

/--
Cold-start advance-safe generated histories preserve the active-rank
no-overshoot invariant through the final state; the canonical initial state
supplies the initial invariant.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_preserves_state_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1)) :
    ∀ rank,
      finalState.IsActive rank →
        finalState.clockPrice ≤
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_preserves_state_no_overshoot
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)

/--
Generated named-strategy histories satisfy exact finite `B*` dropout records
when every clock advance is active-rank safe and the initial state has not
already overshot any active rank's finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_to_no_overshoot_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_no_overshoot_strategy_history
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe)
      hstate_no_overshoot

/--
Generated named-strategy histories satisfy exact finite `B*` dropout records
when every clock advance is active-rank safe and the initial state has not
already overshot any active rank's finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_exact_drop_history
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe)
      hstate_no_overshoot

/--
Advance-safe ordinary named-strategy histories give the exact terminal record for
any rank that starts active and is inactive at the final state.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_final_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hinitial_active : state.IsActive rank)
    (hfinal_inactive : ¬ finalState.IsActive rank) :
    finalState.lastDropout rank =
      some
        (paper_theorem8_bstar_threshold_bid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_final_record_eq_threshold
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
        model hhist hadvance_safe hstate_no_overshoot)
      hinitial_active hfinal_inactive

/--
If an advance-safe ordinary named-strategy history starts with every rank active
and ends with no active ranks, every final dropout record is the corresponding
finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_terminal_records_eq_thresholds
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hinitial_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    ∀ rank,
      finalState.lastDropout rank =
        some
          (paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1)) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_terminal_records_eq_thresholds
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
        model hhist hadvance_safe hstate_no_overshoot)
      hinitial_active hno_active

/--
Generated named-strategy terminal certificate from advance safety. This packages
the concrete history into the no-overshoot terminal-history certificate consumed
by terminal-record endpoints.
-/
def paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_strategy_history_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
    model
    (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
      model hhist hadvance_safe)
    hstate_no_overshoot terminal initially_active

/--
Cold-start generated-history no-overshoot bridge. The canonical cold-start
state supplies the initial no-overshoot fact.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_to_no_overshoot_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_to_no_overshoot_strategy_history
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)

/--
Cold-start generated-history exact-record bridge. The canonical cold-start
state supplies the initial no-overshoot fact.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)

/--
Cold-start advance-safe generated histories give the exact terminal record for
any rank that is inactive at the final state.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_final_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    {rank : ℕ}
    (hfinal_inactive : ¬ finalState.IsActive rank) :
    finalState.lastDropout rank =
      some
        (paper_theorem8_bstar_threshold_bid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_final_record_eq_threshold
      model
      (paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_exact_drop_history
        model hvalue_nonneg hclick_mono hhist hadvance_safe)
      (by rfl) hfinal_inactive

/--
Cold-start advance-safe generated histories with no active final ranks record
every rank's finite `B*` threshold at the final state.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_terminal_records_eq_thresholds
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    ∀ rank,
      finalState.lastDropout rank =
        some
          (paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1)) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_terminal_records_eq_thresholds
      model
      (paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_exact_drop_history
        model hvalue_nonneg hclick_mono hhist hadvance_safe)
      (fun _rank => by rfl) hno_active

/--
Cold-start generated-history terminal certificate from advance safety.
-/
def paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_cold_start_strategy_history_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_strategy_history_advance_safe
    model hhist hadvance_safe
    (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
      model hvalue_nonneg hclick_mono model.click_pos)
    terminal
    (fun rank => by rfl)

/--
Generated named-strategy histories with advance safety discharge both source
obligations used downstream: source-extensive rationality and exact finite
`B*` records. Terminality supplies the generated source path's terminal
component.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model state finalState := by
  exact
    ⟨⟨paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality
          model state,
        hhist,
        terminal⟩,
      paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
        model hhist hadvance_safe hstate_no_overshoot⟩

/--
Cold-start generated-history source/exact ledger. This is the cold-start
version of the previous bridge with initial no-overshoot discharged internally.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_source_extensive_exact_drop_obligations
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal

/--
Source-extensive rationality plus advance safety gives the trace-refined
all-terminal source-extensive VCG conclusion once the initial no-overshoot,
initial activity, and final no-active obligations are supplied. This is the
conditional source theorem left after isolating the real clock-discipline
premise.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
        model hsource_extensive hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace hstate_no_overshoot hsource_extensive.2.2
        initially_active
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_clock_disciplined_strategy_trace
      model
      (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
        model hsource_extensive hadvance_safe)
      hstate_no_overshoot hsource_extensive.2.2 initially_active hno_active

/--
Source-extensive rationality plus advance safety gives the trace-refined
all-terminal belief-explicit VCG conclusion once the initial no-overshoot,
initial activity, and final no-active obligations are supplied.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_belief_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
        model hsource_extensive hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace hstate_no_overshoot hsource_extensive.2.2
        initially_active
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_clock_disciplined_strategy_trace
      model
      (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
        model hsource_extensive hadvance_safe)
      hstate_no_overshoot hsource_extensive.2.2 initially_active hno_active

/--
Generated-history version of the advance-safe all-terminal source-extensive
theorem. The caller supplies the concrete generated history and terminality;
the source-extensive rationality record is built internally from the named
strategy's source-sequential-rationality theorem.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace hstate_no_overshoot terminal initially_active
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  have hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) := by
    exact
      ⟨paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality
          model state,
        hhist,
        terminal⟩
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe hstate_no_overshoot
      initially_active hno_active

/--
Generated-history version for the belief-explicit all-terminal checker.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_belief_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace hstate_no_overshoot terminal initially_active
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  have hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) := by
    exact
      ⟨paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality
          model state,
        hhist,
        terminal⟩
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe hstate_no_overshoot
      initially_active hno_active

/--
Cold-start source-extensive advance-safe all-terminal theorem. The EOS
cold-start state discharges initial no-overshoot and initial activity, so the
remaining source obligations are source-extensive rationality, advance safety,
and final all-ranks inactivity.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_advance_safe_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
        model hsource_extensive hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          model hvalue_nonneg hclick_mono model.click_pos)
        hsource_extensive.2.2
        (fun rank => by rfl)
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      (fun rank => by rfl) hno_active

/--
Cold-start belief-explicit counterpart of the advance-safe all-terminal source
theorem. Initial no-overshoot and activity are derived from the EOS cold-start
state before feeding the non-vacuous belief checker.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_advance_safe_belief_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
        model hsource_extensive hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          model hvalue_nonneg hclick_mono model.click_pos)
        hsource_extensive.2.2
        (fun rank => by rfl)
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      (fun rank => by rfl) hno_active

/--
Cold-start generated-history version of the advance-safe all-terminal
source-extensive theorem. The caller supplies the concrete generated history,
terminality, advance safety, and final all-ranks inactivity; Lean supplies the
named strategy's source sequential rationality internally.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          model hvalue_nonneg hclick_mono model.click_pos)
        terminal
        (fun rank => by rfl)
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  have hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) := by
    exact
      ⟨paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality
          model paper_theorem8_bstar_ranked_threshold_cold_start_state,
        hhist,
        terminal⟩
  simpa using
    paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_advance_safe_trace_all_terminal_vcg_conclusion
      model hvalue_nonneg hclick_mono hsource_extensive hadvance_safe
      hno_active

/--
Cold-start generated-history version for the belief-explicit checker. This is
the non-vacuous belief counterpart of the source-extensive theorem above.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_belief_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model htrace
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          model hvalue_nonneg hclick_mono model.click_pos)
        terminal
        (fun rank => by rfl)
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
        terminalCert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminalCert.initialState terminalCert.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminalCert.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminalCert.localModel terminalCert.initialState
                  terminalCert.finalState ∧
                G.outcomeOf strategy = G.vcgOutcome ∧
                  (∀ rank,
                    (G.outcomeOf strategy).slotOf rank =
                        G.vcgOutcome.slotOf rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        G.vcgOutcome.paymentPerClick rank) ∧
                    ∀ bidder,
                      (G.outcomeOf strategy).utility G.environment G.values
                          bidder =
                        G.vcgOutcome.utility G.environment G.values bidder := by
  have hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) := by
    exact
      ⟨paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality
          model paper_theorem8_bstar_ranked_threshold_cold_start_state,
        hhist,
        terminal⟩
  simpa using
    paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hvalue_nonneg hclick_mono hsource_extensive hadvance_safe
      hno_active

end Auction
end EconCSLib
