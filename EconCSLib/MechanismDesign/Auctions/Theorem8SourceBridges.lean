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
History-local advance safety for an ordinary generated named-strategy history.
Unlike the older global `advance_safe` premise, this proof object only asks for
active-rank clock safety on the concrete transition proof carried by the
history.
-/
inductive PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ} →
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState → Prop
  | refl (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe model
        (PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.refl
          state)
  | cons {state mid finalState :
        PaperTheorem8GeneralizedEnglishAuctionState ℕ}
      (hstep :
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          state mid)
      {htail :
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          mid finalState}
      (hstep_safe :
        ∀ newPrice,
          mid =
            PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
              state newPrice →
            ∀ rank,
              state.IsActive rank →
                newPrice ≤
                  paper_theorem8_bstar_threshold_bid
                    model.value model.clickThroughRate
                    (model.remaining + 1) (rank + 1))
      (htail_safe :
        PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
          model htail) :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe model
        (PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.cons
          hstep htail)

/--
Ordinary cold-start strategy steps alone do not imply advance safety: the
ordinary source transition relation permits advancing the clock past any
chosen active rank's finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_step_allows_unsafe_advance
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (rank : ℕ) :
    let state := paper_theorem8_bstar_ranked_threshold_cold_start_state
    let threshold :=
      paper_theorem8_bstar_threshold_bid
        model.value model.clickThroughRate (model.remaining + 1) (rank + 1)
    ∃ newPrice : ℝ,
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          state
          (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            state newPrice) ∧
        state.IsActive rank ∧
          ¬ newPrice ≤ threshold := by
  dsimp
  let state := paper_theorem8_bstar_ranked_threshold_cold_start_state
  let threshold :=
    paper_theorem8_bstar_threshold_bid
      model.value model.clickThroughRate (model.remaining + 1) (rank + 1)
  let newPrice : ℝ := max 0 (threshold + 1)
  have hclock : state.clockPrice ≤ newPrice := by
    have hstate_clock : state.clockPrice ≤ 0 := by
      norm_num [state, paper_theorem8_bstar_ranked_threshold_cold_start_state]
    exact le_trans hstate_clock (le_max_left _ _)
  refine
    ⟨newPrice,
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep.advance
        state newPrice hclock,
      ?_,
      ?_⟩
  · simp [paper_theorem8_bstar_ranked_threshold_cold_start_state,
      PaperTheorem8GeneralizedEnglishAuctionState.IsActive]
  · intro hsafe
    have hright : threshold + 1 ≤ newPrice := le_max_right _ _
    linarith

/--
The global advance-safety premise used by the clock-disciplined bridge is a
genuine extra source-timing obligation: ordinary cold-start named-strategy
steps do not imply it.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_step_not_global_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (rank : ℕ) :
    ¬
      (∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
        ∀ activeRank,
          stepState.IsActive activeRank →
            newPrice ≤
              paper_theorem8_bstar_threshold_bid
                model.value model.clickThroughRate
                (model.remaining + 1) (activeRank + 1)) := by
  intro hglobal
  rcases
    paper_theorem8_bstar_ranked_threshold_cold_start_strategy_step_allows_unsafe_advance
      model rank with
    ⟨newPrice, hstep, hactive, hunsafe⟩
  exact hunsafe (hglobal hstep rfl rank hactive)

/--
The older global advance-safety premise implies the history-local predicate.
This keeps previous callers compatible while allowing new source bridges to
state only the local obligation they actually use.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_on_history_of_global
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
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
      model hhist := by
  induction hhist with
  | refl state =>
      exact
        PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.refl
          state
  | @cons stepState stepNext finalState hstep htail ih =>
      exact
        PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.cons
          hstep
          (by
            intro newPrice hnext rank hactive
            exact
              hadvance_safe
                (stepState := stepState) (stepNext := stepNext)
                (newPrice := newPrice) hstep hnext rank hactive)
          ih

/--
History-local advance safety is exactly what is needed to convert an ordinary
generated history into an explicit clock-disciplined trace.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  induction hadvance_safe with
  | refl state =>
      exact
        PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace.refl
          state
  | cons hstep hstep_safe htail_safe ih =>
      exact
        PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace.cons
          (paper_theorem8_bstar_ranked_threshold_strategy_step_to_clock_disciplined_strategy_step_of_advance_safe
            model hstep hstep_safe)
          ih

/--
History-local advance safety also supplies the existing clock-disciplined
strategy-history object.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_history_of_history_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_clock_disciplined_strategy_history
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
        model hhist hadvance_safe)

/--
Conversely, every explicit clock-disciplined trace can be forgotten to an
ordinary generated history while retaining history-local advance safety. This
shows the local-safety proof object is exactly the extra evidence carried by
the clock-disciplined source trace.
-/
theorem paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_strategy_history_local_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState) :
    ∃ hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState,
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist := by
  induction htrace with
  | refl state =>
      exact
        ⟨PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.refl
            state,
          PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.refl
            state⟩
  | @cons state mid finalState hstep htail ih =>
      rcases ih with ⟨htail_hist, htail_safe⟩
      cases hstep with
      | advance newPrice hclock hsafe =>
          let hstep' :
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
                (paper_theorem8_bstar_ranked_threshold_strategy
                  model.value model.clickThroughRate model.remaining)
                state
                (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
                  state newPrice) :=
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep.advance
              state newPrice hclock
          refine
            ⟨PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.cons
                hstep' htail_hist,
              PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.cons
                hstep' ?_ htail_safe⟩
          intro realizedPrice hnext rank hactive
          have hprice : newPrice = realizedPrice := by
            have hclock_eq :=
              congrArg
                (fun s : PaperTheorem8GeneralizedEnglishAuctionState ℕ =>
                  s.clockPrice) hnext
            simpa [PaperTheorem8GeneralizedEnglishAuctionState.advanceClock]
              using hclock_eq
          simpa [hprice] using hsafe rank hactive
      | dropout dropRank hactive_drop hstrategy =>
          let hstep' :
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
                (paper_theorem8_bstar_ranked_threshold_strategy
                  model.value model.clickThroughRate model.remaining)
                state
                (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout
                  state dropRank) :=
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep.dropout
              state dropRank hactive_drop hstrategy
          refine
            ⟨PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.cons
                hstep' htail_hist,
              PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.cons
                hstep' ?_ htail_safe⟩
          intro realizedPrice hnext rank hactive
          exfalso
          have hactive_after :
              (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
                state realizedPrice).IsActive dropRank := by
            simpa [PaperTheorem8GeneralizedEnglishAuctionState.advanceClock]
              using hactive_drop
          have hinactive_after :
              ¬ (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout
                state dropRank).IsActive dropRank := by
            simp [PaperTheorem8GeneralizedEnglishAuctionState.recordDropout,
              PaperTheorem8GeneralizedEnglishAuctionState.IsActive]
          exact hinactive_after (by simpa [hnext] using hactive_after)

/--
Every clock-disciplined source history can be forgotten to an ordinary
generated history while retaining history-local advance safety. This is the
history-level analogue of the trace bridge above.
-/
theorem paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_to_strategy_history_local_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState) :
    ∃ hordinary :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState,
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hordinary := by
  induction hhist with
  | refl state =>
      exact
        ⟨PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.refl
            state,
          PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.refl
            state⟩
  | @advance state finalState newPrice hclock hsafe htail ih =>
      rcases ih with ⟨htail_hist, htail_safe⟩
      let hstep' :
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
            (paper_theorem8_bstar_ranked_threshold_strategy
              model.value model.clickThroughRate model.remaining)
            state
            (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
              state newPrice) :=
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep.advance
          state newPrice hclock
      refine
        ⟨PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.cons
            hstep' htail_hist,
          PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.cons
            hstep' ?_ htail_safe⟩
      intro realizedPrice hnext rank hactive
      have hprice : newPrice = realizedPrice := by
        have hclock_eq :=
          congrArg
            (fun s : PaperTheorem8GeneralizedEnglishAuctionState ℕ =>
              s.clockPrice) hnext
        simpa [PaperTheorem8GeneralizedEnglishAuctionState.advanceClock]
          using hclock_eq
      simpa [hprice] using hsafe rank hactive
  | @dropout state finalState dropRank hactive_drop hstrategy htail ih =>
      rcases ih with ⟨htail_hist, htail_safe⟩
      let hstep' :
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
            (paper_theorem8_bstar_ranked_threshold_strategy
              model.value model.clickThroughRate model.remaining)
            state
            (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout
              state dropRank) :=
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep.dropout
          state dropRank hactive_drop hstrategy
      refine
        ⟨PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory.cons
            hstep' htail_hist,
          PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe.cons
            hstep' ?_ htail_safe⟩
      intro realizedPrice hnext rank hactive
      exfalso
      have hactive_after :
          (PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            state realizedPrice).IsActive dropRank := by
        simpa [PaperTheorem8GeneralizedEnglishAuctionState.advanceClock]
          using hactive_drop
      have hinactive_after :
          ¬ (PaperTheorem8GeneralizedEnglishAuctionState.recordDropout
            state dropRank).IsActive dropRank := by
        simp [PaperTheorem8GeneralizedEnglishAuctionState.recordDropout,
          PaperTheorem8GeneralizedEnglishAuctionState.IsActive]
      exact hinactive_after (by simpa [hnext] using hactive_after)

/--
Clock-sorted finite exact-drop schedules produce an ordinary generated history
bundled with the history-local advance-safety proof. This connects the
paper-facing finite schedule data to the local source-semantics bridge without
using the stronger global advance-safety premise.
-/
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_strategy_history_local_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hnodup : ranks.Nodup)
    (hinitial_active : ∀ rank, rank ∈ ranks → state.IsActive rank)
    (hunscheduled_active_threshold :
      ∀ scheduledRank,
        scheduledRank ∈ ranks →
          ∀ otherRank,
            otherRank ∉ ranks →
              state.IsActive otherRank →
                paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    model scheduledRank ≤
                  paper_theorem8_bstar_threshold_bid
                    model.value model.clickThroughRate (model.remaining + 1)
                    (otherRank + 1)) :
    ∃ hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_strategy_history_local_advance_safe
      model
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_clock_disciplined_strategy_trace
        model state ranks hsorted hnodup hinitial_active
        hunscheduled_active_threshold)

/--
Clock-sorted finite exact-drop schedules produce an ordinary generated
history/local-safety pair using only the final unscheduled-rank clock bound.
-/
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_strategy_history_local_advance_safe_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hnodup : ranks.Nodup)
    (hinitial_active : ∀ rank, rank ∈ ranks → state.IsActive rank)
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks).clockPrice <
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∃ hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_strategy_history_local_advance_safe
      model state ranks hsorted hnodup hinitial_active
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_active_threshold_of_final_clock_lt_unscheduled
        model state ranks hsorted hterminal_unscheduled)

/--
History-local advance safety plus initial no-overshoot gives the existing
no-overshoot history object.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_to_no_overshoot_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
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
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
        model hhist hadvance_safe)
      hstate_no_overshoot

/--
History-local advance safety plus initial no-overshoot gives exact finite
`B*` dropout records for the generated history.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
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
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
        model hhist hadvance_safe)
      hstate_no_overshoot

/--
Cold-start history-local advance safety gives the no-overshoot history object;
initial no-overshoot is derived from the EOS cold-start assumptions.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_to_no_overshoot_strategy_history
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_to_no_overshoot_strategy_history
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)

/--
Cold-start history-local advance safety gives exact finite `B*` dropout
records; initial no-overshoot is derived from the EOS cold-start assumptions.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_exact_drop_history
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_exact_drop_history
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)

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
An ordinary named-strategy history whose clock advances are active-rank safe can
be reused as a clock-disciplined history. This is the history-form companion to
the trace bridge and is the shape consumed by several terminal-dynamic endpoints.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_history_of_advance_safe
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
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_clock_disciplined_strategy_history
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
        model hhist hadvance_safe)

/--
Build the strict ordered no-overshoot terminal/dynamic certificate directly from
an ordinary generated history plus advance safety. This lets source proofs feed
the terminal-dynamic endpoints without manually constructing the intermediate
clock-disciplined history.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            dynamic.base.strictModel.value
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  dynamic.base.strictModel.value
                  dynamic.base.strictModel.clickThroughRate
                  (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
      Belief :=
  paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
    dynamic
    (by
      simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
        paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_history_of_advance_safe
          (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
            dynamic.base.strictModel)
          hhist
          (by
            intro stepState stepNext newPrice hstep hnext rank hactive
            simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
              hadvance_safe hstep hnext rank hactive))
    (by
      intro rank hactive
      simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
        hstate_no_overshoot rank hactive)
    terminal initially_active

/--
Build the no-overshoot terminal/dynamic certificate from an ordinary generated
history plus history-local advance safety. This is the weaker source-facing
variant of the global advance-safe certificate constructor.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hhist)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
      Belief :=
  paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
    dynamic
    (by
      simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
        paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_history_of_history_advance_safe
          (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
            dynamic.base.strictModel)
          hhist hadvance_safe)
    (by
      intro rank hactive
      simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
        hstate_no_overshoot rank hactive)
    terminal initially_active

/--
Source-iff full-conclusion endpoint from an ordinary generated history plus
advance safety. The history and advance-safety premises build the
no-overshoot terminal/dynamic certificate internally, leaving the source proof
with only belief consistency, the source-sequential-rationality iff, terminal
inactivity, and outcome/VCG identification.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_source_iff_full_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            dynamic.base.strictModel.value
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  dynamic.base.strictModel.value
                  dynamic.base.strictModel.clickThroughRate
                  (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            state
            strategy)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        dynamic.base.game.PerfectBayesianEquilibrium strategy →
          dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome finalState)
    (hvcg :
      dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
          (dynamic.base.strictModel.remaining + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      (by
        intro rank
        simpa using hno_active rank)
      (by
        intro strategy hpbe
        simpa using houtcome strategy hpbe)
      hvcg

/--
Cold-start specialization of the advance-safe source-iff full endpoint. The
paper cold-start state supplies initial activity and initial no-overshoot; the
remaining source-side history condition is advance safety.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_source_iff_full_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    (hvalue_nonneg :
      ∀ rank, 0 ≤ dynamic.base.strictModel.value rank)
    (hclick_mono :
      ∀ rank,
        dynamic.base.strictModel.clickThroughRate (rank + 1) ≤
          dynamic.base.strictModel.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            dynamic.base.strictModel.value
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  dynamic.base.strictModel.value
                  dynamic.base.strictModel.clickThroughRate
                  (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            paper_theorem8_bstar_ranked_threshold_cold_start_state
            strategy)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        dynamic.base.game.PerfectBayesianEquilibrium strategy →
          dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome finalState)
    (hvcg :
      dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
          (dynamic.base.strictModel.remaining + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
        dynamic hhist hadvance_safe
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
            dynamic.base.strictModel)
          hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
        terminal (fun rank => by rfl)
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_source_iff_full_conclusion
      dynamic hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
      terminal (fun rank => by rfl)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      hno_active houtcome hvcg

/--
Advance-safe generated-history source-iff endpoint with completed-rank terminal
record formulas. The terminal clock cutoff supplies the completed-rank
inactivity proof after the generated history has been converted to a
no-overshoot terminal/dynamic certificate.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            dynamic.base.strictModel.value
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  dynamic.base.strictModel.value
                  dynamic.base.strictModel.clickThroughRate
                  (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            state
            strategy)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          integrated strategy ∧
          ∀ rank,
            rank ∈ completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.terminal.finalState).paymentPerClick rank =
                  paper_theorem8_bstar_threshold_bid
                    cert.terminal.localModel.value
                    cert.terminal.localModel.clickThroughRate
                    (cert.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.terminal.localModel.value
                      cert.terminal.localModel.clickThroughRate
                      rank
                      (cert.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ≤
                        cert.terminal.localModel.value rank := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      completedRanks
      (by
        intro rank hrank
        exact
          (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_inactive_iff_threshold_le_clock
            (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
              dynamic hhist hadvance_safe hstate_no_overshoot terminal
              initially_active).terminal rank).mpr
            (by
              simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
                hcompleted_threshold_le rank hrank))

/--
Cold-start specialization of the advance-safe completed-rank source-iff
endpoint. Initial no-overshoot and activity are derived from the paper
cold-start state.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    (hvalue_nonneg :
      ∀ rank, 0 ≤ dynamic.base.strictModel.value rank)
    (hclick_mono :
      ∀ rank,
        dynamic.base.strictModel.clickThroughRate (rank + 1) ≤
          dynamic.base.strictModel.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      ∀ {stepState stepNext : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {newPrice : ℝ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            dynamic.base.strictModel.value
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.remaining)
          stepState stepNext →
        stepNext =
          PaperTheorem8GeneralizedEnglishAuctionState.advanceClock
            stepState newPrice →
          ∀ rank,
            stepState.IsActive rank →
              newPrice ≤
                paper_theorem8_bstar_threshold_bid
                  dynamic.base.strictModel.value
                  dynamic.base.strictModel.clickThroughRate
                  (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            paper_theorem8_bstar_ranked_threshold_cold_start_state
            strategy)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_advance_safe
        dynamic hhist hadvance_safe
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
            dynamic.base.strictModel)
          hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
        terminal (fun rank => by rfl)
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          integrated strategy ∧
          ∀ rank,
            rank ∈ completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.terminal.finalState).paymentPerClick rank =
                  paper_theorem8_bstar_threshold_bid
                    cert.terminal.localModel.value
                    cert.terminal.localModel.clickThroughRate
                    (cert.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.terminal.localModel.value
                      cert.terminal.localModel.clickThroughRate
                      rank
                      (cert.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ≤
                        cert.terminal.localModel.value rank := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_source_iff_completed_threshold_conclusion
      dynamic hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
      terminal (fun rank => by rfl) concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      completedRanks hcompleted_threshold_le

/--
Clock-disciplined source-iff endpoint for the full terminal/dynamic conclusion.
The terminal history is packaged into the no-overshoot certificate internally,
so callers only supply the source-sequential iff and dynamic-game facts.
-/
theorem paper_theorem8_bstar_ranked_threshold_clock_disciplined_terminal_history_source_iff_full_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            state
            strategy)
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        dynamic.base.game.PerfectBayesianEquilibrium strategy →
          dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome finalState)
    (hvcg :
      dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
          (dynamic.base.strictModel.remaining + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist hstate_no_overshoot terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist hstate_no_overshoot terminal initially_active)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      (by
        intro rank
        simpa using hno_active rank)
      (by
        intro strategy hpbe
        simpa using houtcome strategy hpbe)
      hvcg

/--
Clock-disciplined source-iff endpoint with finite completed-rank formulas. The
terminal clock cutoff is converted internally into completed-rank inactivity.
-/
theorem paper_theorem8_bstar_ranked_threshold_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            state
            strategy)
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist hstate_no_overshoot terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          integrated strategy ∧
          ∀ rank,
            rank ∈ completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.terminal.finalState).paymentPerClick rank =
                  paper_theorem8_bstar_threshold_bid
                    cert.terminal.localModel.value
                    cert.terminal.localModel.clickThroughRate
                    (cert.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.terminal.localModel.value
                      cert.terminal.localModel.clickThroughRate
                      rank
                      (cert.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ≤
                        cert.terminal.localModel.value rank := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist hstate_no_overshoot terminal initially_active)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      completedRanks
      (by
        intro rank hrank
        exact
          (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_inactive_iff_threshold_le_clock
            (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
              dynamic hhist hstate_no_overshoot terminal initially_active).terminal
            rank).mpr
            (by
              simpa [paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history,
                paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
                hcompleted_threshold_le rank hrank))

/--
Cold-start clock-disciplined source-iff endpoint for the full terminal/dynamic
conclusion. Initial no-overshoot and activity are supplied by the cold start.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_terminal_history_source_iff_full_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            paper_theorem8_bstar_ranked_threshold_cold_start_state
            strategy)
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        dynamic.base.game.PerfectBayesianEquilibrium strategy →
          dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome finalState)
    (hvcg :
      dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
          (dynamic.base.strictModel.remaining + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
        dynamic hhist terminal
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa [paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
        dynamic hhist terminal)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      (by
        intro rank
        simpa using hno_active rank)
      (by
        intro strategy hpbe
        simpa using houtcome strategy hpbe)
      hvcg

/--
Cold-start clock-disciplined source-iff endpoint with finite completed-rank
formulas. The terminal clock cutoff proves completed-rank inactivity internally.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            paper_theorem8_bstar_ranked_threshold_cold_start_state
            strategy)
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
        dynamic hhist terminal
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          integrated strategy ∧
          ∀ rank,
            rank ∈ completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.terminal.finalState).paymentPerClick rank =
                  paper_theorem8_bstar_threshold_bid
                    cert.terminal.localModel.value
                    cert.terminal.localModel.clickThroughRate
                    (cert.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.terminal.localModel.value
                      cert.terminal.localModel.clickThroughRate
                      rank
                      (cert.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ≤
                        cert.terminal.localModel.value rank := by
  simpa [paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history,
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
        dynamic hhist terminal)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      completedRanks
      (by
        intro rank hrank
        exact
          (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_inactive_iff_threshold_le_clock
            (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
              dynamic hhist terminal).terminal
            rank).mpr
            (by
              simpa [paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history,
                paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
                hcompleted_threshold_le rank hrank))

/--
Source-iff full-conclusion endpoint from an ordinary generated history plus
history-local advance safety. This is the source-semantics bridge with the
local clock-safety obligation isolated to the concrete history being checked.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_source_iff_full_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hhist)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            state
            strategy)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        dynamic.base.game.PerfectBayesianEquilibrium strategy →
          dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome finalState)
    (hvcg :
      dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
          (dynamic.base.strictModel.remaining + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      (by
        intro rank
        simpa using hno_active rank)
      (by
        intro strategy hpbe
        simpa using houtcome strategy hpbe)
      hvcg

/--
Cold-start full source-iff endpoint from an ordinary generated history plus
history-local advance safety. Initial no-overshoot and activity are derived
from the paper cold-start state.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_source_iff_full_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    (hvalue_nonneg :
      ∀ rank, 0 ≤ dynamic.base.strictModel.value rank)
    (hclick_mono :
      ∀ rank,
        dynamic.base.strictModel.clickThroughRate (rank + 1) ≤
          dynamic.base.strictModel.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hhist)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            paper_theorem8_bstar_ranked_threshold_cold_start_state
            strategy)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        dynamic.base.game.PerfectBayesianEquilibrium strategy →
          dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome finalState)
    (hvcg :
      dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
          (dynamic.base.strictModel.remaining + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
        dynamic hhist hadvance_safe
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
            dynamic.base.strictModel)
          hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
        terminal (fun rank => by rfl)
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_source_iff_full_conclusion
      dynamic hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
      terminal (fun rank => by rfl)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      hno_active houtcome hvcg

/--
History-local advance-safe source-iff endpoint with completed-rank terminal
record formulas. This is the finite-rank counterpart of the local full
source-iff bridge.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hhist)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value
              dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            state
            strategy)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          integrated strategy ∧
          ∀ rank,
            rank ∈ completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.terminal.finalState).paymentPerClick rank =
                  paper_theorem8_bstar_threshold_bid
                    cert.terminal.localModel.value
                    cert.terminal.localModel.clickThroughRate
                    (cert.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.terminal.localModel.value
                      cert.terminal.localModel.clickThroughRate
                      rank
                      (cert.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ≤
                        cert.terminal.localModel.value rank := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
        dynamic hhist hadvance_safe hstate_no_overshoot terminal initially_active)
      concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      completedRanks
      (by
        intro rank hrank
        exact
          (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_inactive_iff_threshold_le_clock
            (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
              dynamic hhist hadvance_safe hstate_no_overshoot terminal
              initially_active).terminal rank).mpr
            (by
              simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
                hcompleted_threshold_le rank hrank))

/--
Cold-start local advance-safe source-iff endpoint with completed-rank terminal
record formulas. Initial no-overshoot and activity are derived from the paper
cold-start state.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (dynamic :
      PaperTheorem8BStarRankedThresholdStrictOrderedDynamicGameConstructedOutcomeCertificate
        Belief)
    (hvalue_nonneg :
      ∀ rank, 0 ≤ dynamic.base.strictModel.value rank)
    (hclick_mono :
      ∀ rank,
        dynamic.base.strictModel.clickThroughRate (rank + 1) ≤
          dynamic.base.strictModel.clickThroughRate rank)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hhist)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        finalState)
    (concrete_belief_consistency :
      dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          dynamic.base.strictModel.value
          dynamic.base.strictModel.clickThroughRate
          dynamic.base.strictModel.remaining)
        dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            dynamic.base.strictModel.clickThroughRate
            dynamic.base.strictModel.value
            dynamic.base.strictModel.remaining
            paper_theorem8_bstar_ranked_threshold_cold_start_state
            strategy)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_strategy_history_local_advance_safe
        dynamic hhist hadvance_safe
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
            dynamic.base.strictModel)
          hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
        terminal (fun rank => by rfl)
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          integrated strategy ∧
          ∀ rank,
            rank ∈ completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.terminal.finalState).paymentPerClick rank =
                  paper_theorem8_bstar_threshold_bid
                    cert.terminal.localModel.value
                    cert.terminal.localModel.clickThroughRate
                    (cert.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.terminal.localModel.value
                      cert.terminal.localModel.clickThroughRate
                      rank
                      (cert.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.terminal.finalState).paymentPerClick rank ≤
                        cert.terminal.localModel.value rank := by
  simpa [paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_source_iff_completed_threshold_conclusion
      dynamic hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          dynamic.base.strictModel)
        hvalue_nonneg hclick_mono dynamic.base.strictModel.click_pos)
      terminal (fun rank => by rfl) concrete_belief_consistency
      (by
        intro strategy belief
        simpa using
          sequential_rationality_iff_source_sequential strategy belief)
      completedRanks hcompleted_threshold_le

/--
Generated named-strategy histories package directly as the source-extensive
rationality statement used by the source-facing endpoints. Terminality supplies
the terminal component; the named finite `B*` source-sequential rationality is
internal to the construction.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
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
        finalState) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
      model state finalState
      (paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining) := by
  exact
    ⟨paper_theorem8_bstar_ranked_threshold_named_strategy_source_sequential_rationality
        model state,
      hhist,
      terminal⟩

/--
Generated named-strategy histories with history-local advance safety discharge
the downstream source-extensive/exact-drop obligation ledger. This is the
local-safety version of the earlier global advance-safe obligation theorem.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
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
    ⟨paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal,
      paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_exact_drop_history
        model hhist hadvance_safe hstate_no_overshoot⟩

/--
Cold-start local-safety source-extensive/exact-drop obligation ledger. Initial
no-overshoot is derived from the EOS cold-start assumptions.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_source_extensive_exact_drop_obligations
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
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
    paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_source_extensive_exact_drop_obligations
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal

/--
Source-extensive rationality packages a generated history; if that concrete
history has local advance-safety evidence, it yields an explicit
clock-disciplined trace.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
      model hsource_extensive.2.1 hadvance_safe

/--
Clock-disciplined histories can be packaged as source-extensive rationality
records whose generated-history component carries matching history-local
advance-safety evidence.
-/
theorem paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_source_extensive_local_advance_safe_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    ∃ hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1 := by
  rcases
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_to_strategy_history_local_advance_safe
      model hhist with ⟨hordinary, hadvance_safe⟩
  exact
    ⟨paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hordinary terminal,
    hadvance_safe⟩

/--
Clock-disciplined traces have the same matching source-extensive/local-safety
obligation package as clock-disciplined histories.
-/
theorem paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_source_extensive_local_advance_safe_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    ∃ hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1 := by
  rcases
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_strategy_history_local_advance_safe
      model htrace with ⟨hordinary, hadvance_safe⟩
  exact
    ⟨paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hordinary terminal,
    hadvance_safe⟩

/--
Source-extensive rationality plus history-local advance safety discharges the
source-extensive/exact-drop ledger without the older global advance-safe
premise.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model state finalState := by
  exact
    ⟨hsource_extensive,
      paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_exact_drop_history
        model hsource_extensive.2.1 hadvance_safe hstate_no_overshoot⟩

/--
Source-extensive rationality plus history-local advance safety directly builds
the no-overshoot terminal-history certificate used by the terminal-record
source-extensive endpoints. This keeps the generated history, terminality, and
no-overshoot strengthening tied to the same source proof object.
-/
def paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_source_extensive_rationality_local_advance_safe
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_no_overshoot_strategy_history
    model
    (paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_to_no_overshoot_strategy_history
      model hsource_extensive.2.1 hadvance_safe hstate_no_overshoot)
    hsource_extensive.2.2
    initially_active

/--
Cold-start source-extensive/local-safety certificate constructor. Initial
activity and no-overshoot are discharged by the standard EOS cold-start
assumptions.
-/
def paper_theorem8_bstar_ranked_threshold_cold_start_no_overshoot_terminal_history_behavior_certificate_of_source_extensive_rationality_local_advance_safe
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_source_extensive_rationality_local_advance_safe
    model hsource_extensive hadvance_safe
    (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
      model hvalue_nonneg hclick_mono model.click_pos)
    (fun rank => by rfl)

/--
Cold-start source-extensive rationality plus history-local advance safety
discharges the exact-drop ledger, with initial no-overshoot derived from the
paper cold-start assumptions.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_local_advance_safe_exact_drop_obligations
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_exact_drop_obligations
      model hsource_extensive hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)

/--
Clock-sorted no-duplicate finite schedules discharge the compact source ledger
while keeping the generated source history, local advance-safety evidence, and
exact-drop history tied to the same ordinary strategy history.
-/
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_source_extensive_local_advance_safe_exact_drop_obligations_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hnodup : ranks.Nodup)
    (hinitial_active : ∀ rank, rank ∈ ranks → state.IsActive rank)
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks).clockPrice <
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∃ hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
          model hsource_extensive.2.1 ∧
        PaperTheorem8BStarRankedThresholdExactDropHistory
          model state
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks) := by
  rcases
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_strategy_history_local_advance_safe_of_final_clock_lt_unscheduled
      model state ranks hsorted hnodup hinitial_active hterminal_unscheduled with
    ⟨hhist, hadvance_safe⟩
  have hterminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks) :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
      model
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
        model state ranks hsorted hnodup hinitial_active)
      hterminal_unscheduled
  let hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) :=
    paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
      model hhist hterminal
  have hledger :=
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_exact_drop_obligations
      model hsource_extensive hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_initial_no_overshoot_of_clock_sorted_final_clock_lt_unscheduled
        model state ranks hsorted hterminal_unscheduled)
  exact ⟨hsource_extensive, hadvance_safe, hledger.2⟩

/--
Cold-start specialization of the clock-sorted finite-schedule source ledger:
initial activity is derived from the empty dropout record, and the final
unscheduled-rank terminality check supplies the initial no-overshoot facts.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_exact_drop_schedule_clock_sorted_nodup_source_extensive_local_advance_safe_exact_drop_obligations_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        ranks)
    (hnodup : ranks.Nodup)
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model paper_theorem8_bstar_ranked_threshold_cold_start_state
            ranks).clockPrice <
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∃ hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
          model hsource_extensive.2.1 ∧
        PaperTheorem8BStarRankedThresholdExactDropHistory
          model paper_theorem8_bstar_ranked_threshold_cold_start_state
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model paper_theorem8_bstar_ranked_threshold_cold_start_state
            ranks) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_source_extensive_local_advance_safe_exact_drop_obligations_of_final_clock_lt_unscheduled
      model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks
      hsorted hnodup
      (by
        intro rank _hrank
        rfl)
      hterminal_unscheduled

/--
Strict-ordered cold-start append schedules discharge the same-history
source-extensive, local advance-safety, and exact-drop ledger from the
paper-facing threshold-sorted checks and last-threshold terminality bound.
-/
theorem paper_theorem8_bstar_ranked_threshold_strict_ordered_cold_start_threshold_sorted_append_singleton_source_extensive_local_advance_safe_exact_drop_obligations
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (scheduledPrefix : List ℕ) (lastRank : ℕ)
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (scheduledPrefix ++ [lastRank]))
    (hnodup : (scheduledPrefix ++ [lastRank]).Nodup)
    (hunscheduled_last :
      ∀ rank,
        rank ∉ scheduledPrefix ++ [lastRank] →
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              lastRank <
            paper_theorem8_bstar_threshold_bid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    ∃ hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          (scheduledPrefix ++ [lastRank]))
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
          localModel hsource_extensive.2.1 ∧
        PaperTheorem8BStarRankedThresholdExactDropHistory
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
            (scheduledPrefix ++ [lastRank])) := by
  dsimp
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_exact_drop_schedule_clock_sorted_nodup_source_extensive_local_advance_safe_exact_drop_obligations_of_final_clock_lt_unscheduled
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model)
      (scheduledPrefix ++ [lastRank])
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_of_threshold_sorted
        model (scheduledPrefix ++ [lastRank]) hthreshold_sorted)
      hnodup
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        paper_theorem8_bstar_ranked_threshold_cold_start_state
        scheduledPrefix lastRank hunscheduled_last)

/--
Strict-ordered cold-start append schedules discharge the source ledger and the
trace-refined completed-rank terminal-record conclusion in one source theorem.
This bundles the finite schedule obligations used by source-extensive proofs
with the PBE conclusion used by paper-facing completed-rank checks.
-/
theorem paper_theorem8_bstar_ranked_threshold_strict_ordered_cold_start_threshold_sorted_append_singleton_source_extensive_local_advance_safe_trace_completed_rank_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (completedRanks : Finset ℕ)
    (scheduledPrefix : List ℕ) (lastRank : ℕ)
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (scheduledPrefix ++ [lastRank]))
    (hnodup : (scheduledPrefix ++ [lastRank]).Nodup)
    (hunscheduled_last :
      ∀ rank,
        rank ∉ scheduledPrefix ++ [lastRank] →
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              lastRank <
            paper_theorem8_bstar_threshold_bid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledPrefix ++ [lastRank]) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        (scheduledPrefix ++ [lastRank])
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        (scheduledPrefix ++ [lastRank])
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_of_threshold_sorted
          model (scheduledPrefix ++ [lastRank]) hthreshold_sorted)
        hnodup (fun rank => by rfl)
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          scheduledPrefix lastRank hunscheduled_last)
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
        terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃ hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining),
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
          localModel hsource_extensive.2.1 ∧
        PaperTheorem8BStarRankedThresholdExactDropHistory
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          finalState ∧
          ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
            G.PerfectBayesianEquilibrium strategy ∧
              strategy = namedStrategy ∧
                PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                    strategy terminal.initialState terminal.finalState ∧
                  PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                      strategy terminal.finalState ∧
                    PaperTheorem8BStarRankedThresholdExactDropHistory
                        terminal.localModel terminal.initialState
                        terminal.finalState ∧
                      ∀ rank,
                        rank ∈ completedRanks →
                          (G.outcomeOf strategy).slotOf rank = some rank ∧
                            (G.outcomeOf strategy).paymentPerClick rank =
                              paper_theorem8_bstar_threshold_bid
                                localModel.value localModel.clickThroughRate
                                (localModel.remaining + 1) (rank + 1) ∧
                              localModel.clickThroughRate rank *
                                  (G.outcomeOf strategy).paymentPerClick rank =
                                paper_theorem7_ranked_vcg_tail_payment
                                  localModel.value localModel.clickThroughRate
                                  rank (localModel.remaining + 1) ∧
                                0 ≤ (G.outcomeOf strategy).paymentPerClick rank ∧
                                  (G.outcomeOf strategy).paymentPerClick rank ≤
                                    localModel.value rank := by
  dsimp
  rcases
    paper_theorem8_bstar_ranked_threshold_strict_ordered_cold_start_threshold_sorted_append_singleton_source_extensive_local_advance_safe_exact_drop_obligations
      model scheduledPrefix lastRank hthreshold_sorted hnodup
      hunscheduled_last with
    ⟨hsource_extensive, hadvance_safe, hexact⟩
  refine ⟨hsource_extensive, hadvance_safe, hexact, ?_⟩
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_strict_ordered_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model completedRanks scheduledPrefix lastRank hthreshold_sorted hnodup
      hunscheduled_last hsubset

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
Advance-safe ordinary named-strategy histories close the terminal-record outcome
bridge when every rank starts active and none remain active.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_terminal_record_outcome_eq_bstar
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
    paper_theorem8_terminal_dropout_record_outcome finalState =
      paper_theorem8_bstar_ranked_threshold_outcome
        model.value model.clickThroughRate (model.remaining + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_terminal_record_outcome_eq_bstar
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
        model hhist hadvance_safe hstate_no_overshoot)
      hinitial_active hno_active

/--
Advance-safe ordinary named-strategy histories give the full ordered
terminal-record paper conclusion when every rank starts active and none remain
active.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_terminal_record_ordered_paper_conclusion
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
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono :
      ∀ i, model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    (∀ rank,
      (paper_theorem8_terminal_dropout_record_outcome finalState).slotOf rank =
        some rank) ∧
      (∀ rank,
        (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
            rank =
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1)) ∧
        (∀ rank,
          model.clickThroughRate rank *
              (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
                rank =
            paper_theorem7_ranked_vcg_tail_payment
              model.value model.clickThroughRate rank (model.remaining + 1)) ∧
          (∀ rank,
            0 ≤
              (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
                rank ∧
            (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
                rank ≤ model.value rank) ∧
            (paper_theorem8_terminal_dropout_record_outcome
              finalState).IndividuallyRational
              ({ clickThroughRate := model.clickThroughRate } :
                PositionEnvironment ℕ)
              model.value ∧
              paper_position_no_positive_transfers
                (paper_theorem8_terminal_dropout_record_outcome
                  finalState) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_terminal_record_ordered_paper_conclusion
      model
      (paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_exact_drop_history
        model hhist hadvance_safe hstate_no_overshoot)
      hinitial_active hno_active hvalue_nonneg hvalue_mono hclick_mono
      hclick_pos

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
Cold-start advance-safe generated histories close the terminal-record outcome
bridge when no rank remains active.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_terminal_record_outcome_eq_bstar
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
    paper_theorem8_terminal_dropout_record_outcome finalState =
      paper_theorem8_bstar_ranked_threshold_outcome
        model.value model.clickThroughRate (model.remaining + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_terminal_record_outcome_eq_bstar
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      (fun _rank => by rfl) hno_active

/--
Cold-start advance-safe generated histories give the full ordered terminal-record
paper conclusion when no rank remains active.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_advance_safe_terminal_record_ordered_paper_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono :
      ∀ i, model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i)
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
    (∀ rank,
      (paper_theorem8_terminal_dropout_record_outcome finalState).slotOf rank =
        some rank) ∧
      (∀ rank,
        (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
            rank =
          paper_theorem8_bstar_threshold_bid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1)) ∧
        (∀ rank,
          model.clickThroughRate rank *
              (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
                rank =
            paper_theorem7_ranked_vcg_tail_payment
              model.value model.clickThroughRate rank (model.remaining + 1)) ∧
          (∀ rank,
            0 ≤
              (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
                rank ∧
            (paper_theorem8_terminal_dropout_record_outcome finalState).paymentPerClick
                rank ≤ model.value rank) ∧
            (paper_theorem8_terminal_dropout_record_outcome
              finalState).IndividuallyRational
              ({ clickThroughRate := model.clickThroughRate } :
                PositionEnvironment ℕ)
              model.value ∧
              paper_position_no_positive_transfers
                (paper_theorem8_terminal_dropout_record_outcome
                  finalState) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strategy_history_advance_safe_terminal_record_ordered_paper_conclusion
      model hhist hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono hclick_pos)
      (fun _rank => by rfl) hno_active hvalue_nonneg hvalue_mono hclick_mono
      hclick_pos

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
    ⟨paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal,
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
Source-extensive rationality plus history-local advance safety gives the
trace-refined all-terminal source-extensive VCG conclusion. This is the local
clock-safety version of the older global advance-safe endpoint.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
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
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
      (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
        model hsource_extensive hadvance_safe)
      hstate_no_overshoot hsource_extensive.2.2 initially_active hno_active

/--
Belief-explicit counterpart of the local advance-safe all-terminal
source-extensive VCG theorem.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
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
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
      (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
        model hsource_extensive hadvance_safe)
      hstate_no_overshoot hsource_extensive.2.2 initially_active hno_active

/--
Source-extensive rationality plus history-local advance safety gives the
trace-refined completed-rank paper conclusion for the ordinary
source-extensive terminal-record checker. The completed-rank premise is only
that the terminal clock has reached each reviewed finite `B*` threshold.
-/
theorem paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_trace_completed_rank_paper_conclusion_of_completed_threshold_le
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining))
    (hadvance_safe :
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_source_extensive_rationality_local_advance_safe
        model hsource_extensive hadvance_safe hstate_no_overshoot
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
              strategy state finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  model state finalState ∧
                ∀ rank,
                  rank ∈ completedRanks →
                    (G.outcomeOf strategy).slotOf rank = some rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        paper_theorem8_bstar_threshold_bid
                          model.value model.clickThroughRate
                          (model.remaining + 1) (rank + 1) ∧
                        model.clickThroughRate rank *
                            (G.outcomeOf strategy).paymentPerClick rank =
                          paper_theorem7_ranked_vcg_tail_payment
                            model.value model.clickThroughRate
                            rank (model.remaining + 1) ∧
                          0 ≤ (G.outcomeOf strategy).paymentPerClick rank ∧
                            (G.outcomeOf strategy).paymentPerClick rank ≤
                              model.value rank := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_source_extensive_rationality_local_advance_safe
        model hsource_extensive hadvance_safe hstate_no_overshoot
        initially_active)
      completedRanks hcompleted_threshold_le hvalue_nonneg hvalue_mono
      hclick_mono model.click_pos

/--
Generated-history local-safety completed-rank theorem for the ordinary
source-extensive checker. The named strategy's source sequential rationality is
supplied internally; the completed-rank obligation is a terminal-clock
threshold condition for the finite ranks under review.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_trace_completed_rank_paper_conclusion_of_completed_threshold_le
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_no_overshoot_strategy_history
        model
        (paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_to_no_overshoot_strategy_history
          model hhist hadvance_safe hstate_no_overshoot)
        terminal
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
              strategy state finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  model state finalState ∧
                ∀ rank,
                  rank ∈ completedRanks →
                    (G.outcomeOf strategy).slotOf rank = some rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        paper_theorem8_bstar_threshold_bid
                          model.value model.clickThroughRate
                          (model.remaining + 1) (rank + 1) ∧
                        model.clickThroughRate rank *
                            (G.outcomeOf strategy).paymentPerClick rank =
                          paper_theorem7_ranked_vcg_tail_payment
                            model.value model.clickThroughRate
                            rank (model.remaining + 1) ∧
                          0 ≤ (G.outcomeOf strategy).paymentPerClick rank ∧
                            (G.outcomeOf strategy).paymentPerClick rank ≤
                              model.value rank := by
  have hsource_extensive :
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) := by
    exact
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_trace_completed_rank_paper_conclusion_of_completed_threshold_le
      model hsource_extensive hadvance_safe hstate_no_overshoot
      initially_active completedRanks hcompleted_threshold_le hvalue_nonneg
      hvalue_mono hclick_mono

/--
Generated-history local-safety version of the all-terminal source-extensive
VCG theorem. The named strategy's source-sequential rationality is supplied
internally.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_trace_all_terminal_vcg_conclusion
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe hstate_no_overshoot
      initially_active hno_active

/--
Generated-history local-safety version for the belief-explicit all-terminal
checker.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe hstate_no_overshoot
      initially_active hno_active

/--
Generated-history local-safety completed-rank theorem for the belief-explicit
source-extensive checker. The named strategy's source sequential rationality is
supplied internally; the completed-rank obligation is a terminal-clock
threshold condition for the finite ranks under review.
-/
theorem paper_theorem8_bstar_ranked_threshold_strategy_history_local_advance_safe_belief_trace_completed_rank_paper_conclusion_of_completed_threshold_le
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
                ∀ rank,
                  rank ∈ completedRanks →
                    (G.outcomeOf strategy).slotOf rank = some rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        paper_theorem8_bstar_threshold_bid
                          model.value model.clickThroughRate
                          (model.remaining + 1) (rank + 1) ∧
                        model.clickThroughRate rank *
                            (G.outcomeOf strategy).paymentPerClick rank =
                          paper_theorem7_ranked_vcg_tail_payment
                            model.value model.clickThroughRate
                            rank (model.remaining + 1) ∧
                          0 ≤ (G.outcomeOf strategy).paymentPerClick rank ∧
                            (G.outcomeOf strategy).paymentPerClick rank ≤
                              model.value rank := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_trace
        model
        (paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
          model hhist hadvance_safe)
        hstate_no_overshoot terminal initially_active)
      completedRanks hcompleted_threshold_le hvalue_nonneg hvalue_mono
      hclick_mono model.click_pos

/--
Consistent beliefs in the belief-explicit source-extensive terminal-record game
carry the generated history and terminality proof for the checked strategy.
This exposes the source-history payload directly instead of requiring callers
to unpack a PBE wrapper.
-/
theorem paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_consistent_belief_history_terminal
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    {belief :
      PaperTheorem8BStarRankedThresholdSourceExtensiveBelief
        terminal.initialState terminal.finalState}
    (hconsistent :
      (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
        terminal).isConsistentBelief strategy belief) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        strategy terminal.initialState terminal.finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        strategy terminal.finalState := by
  cases hconsistent
  exact ⟨belief.generated_history, belief.terminal⟩

/--
In the belief-explicit source-extensive terminal-record game, sequential
rationality is exactly the local-deviation target used by the strict ordered
Theorem 8 source-completion certificates.
-/
theorem paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_sequential_rationality_iff_local_deviation
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ)
    (belief :
      PaperTheorem8BStarRankedThresholdSourceExtensiveBelief
        terminal.initialState terminal.finalState) :
    (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
      terminal).isSequentiallyRational strategy belief ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
        terminal.localModel.clickThroughRate terminal.localModel.value
        terminal.localModel.remaining strategy := by
  simpa [paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game] using
    paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation
      terminal.localModel.clickThroughRate terminal.localModel.value
      terminal.localModel.remaining terminal.initialState strategy

/--
Consistent beliefs in the state-based belief-explicit source-extensive
terminal-record game carry the generated history and terminality proof for the
checked strategy. This is the finite-active counterpart of the terminal
certificate extractor above.
-/
theorem paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states_consistent_belief_history_terminal
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState :
      PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    {belief :
      PaperTheorem8BStarRankedThresholdSourceExtensiveBelief
        initialState finalState}
    (hconsistent :
      (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
        model initialState finalState).isConsistentBelief strategy belief) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        strategy initialState finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        strategy finalState := by
  cases hconsistent
  exact ⟨belief.generated_history, belief.terminal⟩

/--
In the state-based belief-explicit source-extensive terminal-record game,
sequential rationality is exactly the local-deviation target for the supplied
finite `B*` model.
-/
theorem paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states_sequential_rationality_iff_local_deviation
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState :
      PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ)
    (belief :
      PaperTheorem8BStarRankedThresholdSourceExtensiveBelief
        initialState finalState) :
    (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
      model initialState finalState).isSequentiallyRational strategy belief ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
        model.clickThroughRate model.value model.remaining strategy := by
  simpa [paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states] using
    paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation
      model.clickThroughRate model.value model.remaining initialState strategy

/--
Exact finite `B*` histories also feed the belief-explicit source-extensive
completed-rank checker directly. The exact history is packaged internally as
the no-overshoot terminal-history certificate used by the belief source game,
and the terminal-clock premise derives completed-rank inactivity.
-/
theorem paper_theorem8_bstar_ranked_threshold_exact_drop_history_belief_source_extensive_trace_completed_rank_paper_conclusion_of_completed_threshold_le
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdExactDropHistory model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let terminalCert :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_exact_drop_history
        model hhist terminal initially_active
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
              strategy state finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  model state finalState ∧
                ∀ rank,
                  rank ∈ completedRanks →
                    (G.outcomeOf strategy).slotOf rank = some rank ∧
                      (G.outcomeOf strategy).paymentPerClick rank =
                        paper_theorem8_bstar_threshold_bid
                          model.value model.clickThroughRate
                          (model.remaining + 1) (rank + 1) ∧
                        model.clickThroughRate rank *
                            (G.outcomeOf strategy).paymentPerClick rank =
                          paper_theorem7_ranked_vcg_tail_payment
                            model.value model.clickThroughRate
                            rank (model.remaining + 1) ∧
                          0 ≤ (G.outcomeOf strategy).paymentPerClick rank ∧
                            (G.outcomeOf strategy).paymentPerClick rank ≤
                              model.value rank := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_exact_drop_history
        model hhist terminal initially_active)
      completedRanks hcompleted_threshold_le hvalue_nonneg hvalue_mono
      hclick_mono model.click_pos

/--
Exact finite `B*` histories plus terminality feed the strict ordered ex-post
local-deviation source-completion endpoint. This is weaker than the
source-extensive variant: local-deviation source completion supplies the
source rationality certificate, so the history side only needs exact records,
terminality, initial activity, and completed-rank terminal-clock evidence.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_drop_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (exact_history :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel state finalState)
    (terminal :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let terminalCert :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate :=
    { localModel := localModel
      initialState := state
      finalState := finalState
      history :=
        paper_theorem8_bstar_ranked_threshold_exact_drop_history_to_strategy_history
          localModel exact_history
      terminal := terminal
      initially_active := initially_active }
  paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_local_deviation
    terminalCert model (by rfl) completedRanks exact_history
    (by
      intro rank hrank
      exact
        (paper_theorem8_bstar_ranked_threshold_terminal_history_behavior_inactive_iff_threshold_le_clock
          terminalCert rank).mpr
          (hcompleted_threshold_le rank hrank))

/--
Trace-rich exact-history source-completion endpoint from terminality alone.
The returned source-completion certificate stores the supplied exact-drop
history and exposes the named strategy, generated history, terminality, exact
drop trace, and completed-rank terminal-record formulas.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_drop_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (exact_history :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel state finalState)
    (terminal :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let terminalCert :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate :=
    { localModel := localModel
      initialState := state
      finalState := finalState
      history :=
        paper_theorem8_bstar_ranked_threshold_exact_drop_history_to_strategy_history
          localModel exact_history
      terminal := terminal
      initially_active := initially_active }
  paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_source_completion_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion
    (paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_source_completion_certificate_of_ex_post_local_deviation
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_certificate_of_local_deviation
        terminalCert model (by rfl) completedRanks exact_history
        (by
          intro rank hrank
          exact
            (paper_theorem8_bstar_ranked_threshold_terminal_history_behavior_inactive_iff_threshold_le_clock
              terminalCert rank).mpr
              (hcompleted_threshold_le rank hrank))))

/--
Payoff-facing exact-history source-completion endpoint from terminality alone:
completed-rank terminal-record utility equals the constructed successor-tail
ranked-`B*` outcome utility.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_drop_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (exact_history :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel state finalState)
    (terminal :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
          model).base.strictModel
    (paper_theorem8_terminal_dropout_record_outcome finalState).utility
        ({ clickThroughRate := localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        localModel.value localModel.clickThroughRate
        (localModel.remaining + 1)).utility
        ({ clickThroughRate := localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        localModel.value rank :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let terminalCert :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate :=
    { localModel := localModel
      initialState := state
      finalState := finalState
      history :=
        paper_theorem8_bstar_ranked_threshold_exact_drop_history_to_strategy_history
          localModel exact_history
      terminal := terminal
      initially_active := initially_active }
  paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_mem
    (paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_certificate_of_local_deviation
      terminalCert model (by rfl) completedRanks exact_history
      (by
        intro completedRank hcompletedRank
        exact
          (paper_theorem8_bstar_ranked_threshold_terminal_history_behavior_inactive_iff_threshold_le_clock
            terminalCert completedRank).mpr
            (hcompleted_threshold_le completedRank hcompletedRank)))
    hrank

/--
Source-extensive rationality plus an exact finite `B*` history feeds the
strict ordered ex-post local-deviation source-completion endpoint. Compared
with the realized-dropout route, callers no longer need a separate no-overshoot
timing statement once they can supply the exact-drop history itself.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_source_extensive_rationality_exact_drop_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining))
    (exact_history :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel state finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let terminal :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate :=
    { localModel := localModel
      initialState := state
      finalState := finalState
      history :=
        paper_theorem8_bstar_ranked_threshold_exact_drop_history_to_strategy_history
          localModel exact_history
      terminal := hsource_extensive.2.2
      initially_active := initially_active }
  paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_local_deviation
    terminal model (by rfl) completedRanks exact_history
    (by
      intro rank hrank
      exact
        (paper_theorem8_bstar_ranked_threshold_terminal_history_behavior_inactive_iff_threshold_le_clock
          terminal rank).mpr
          (hcompleted_threshold_le rank hrank))

/--
Trace-rich exact-history source-completion endpoint. The supplied exact-drop
history is the one stored in the finite source-completion certificate, so the
returned trace witness is tied directly to the source proof obligation.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_source_extensive_rationality_exact_drop_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining))
    (exact_history :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel state finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let terminal :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate :=
    { localModel := localModel
      initialState := state
      finalState := finalState
      history :=
        paper_theorem8_bstar_ranked_threshold_exact_drop_history_to_strategy_history
          localModel exact_history
      terminal := hsource_extensive.2.2
      initially_active := initially_active }
  paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_source_completion_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion
    (paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_source_completion_certificate_of_ex_post_local_deviation
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_certificate_of_local_deviation
        terminal model (by rfl) completedRanks exact_history
        (by
          intro rank hrank
          exact
            (paper_theorem8_bstar_ranked_threshold_terminal_history_behavior_inactive_iff_threshold_le_clock
              terminal rank).mpr
              (hcompleted_threshold_le rank hrank))))

/--
Payoff-facing exact-history source-completion endpoint. The same exact finite
`B*` history and terminal-clock completed-rank premise yield equality between
the terminal dropout-record utility and the constructed successor-tail
ranked-`B*` outcome utility for every completed rank.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_source_extensive_rationality_exact_drop_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining))
    (exact_history :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel state finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
          model).base.strictModel
    (paper_theorem8_terminal_dropout_record_outcome finalState).utility
        ({ clickThroughRate := localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        localModel.value localModel.clickThroughRate
        (localModel.remaining + 1)).utility
        ({ clickThroughRate := localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        localModel.value rank :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let terminal :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate :=
    { localModel := localModel
      initialState := state
      finalState := finalState
      history :=
        paper_theorem8_bstar_ranked_threshold_exact_drop_history_to_strategy_history
          localModel exact_history
      terminal := hsource_extensive.2.2
      initially_active := initially_active }
  paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_mem
    (paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_certificate_of_local_deviation
      terminal model (by rfl) completedRanks exact_history
      (by
        intro completedRank hcompletedRank
        exact
          (paper_theorem8_bstar_ranked_threshold_terminal_history_behavior_inactive_iff_threshold_le_clock
            terminal completedRank).mpr
          (hcompleted_threshold_le completedRank hcompletedRank)))
    hrank

/--
Source-extensive rationality plus matching history-local advance safety feeds
the strict ordered ex-post local-deviation source-completion endpoint. This
removes the explicit exact-drop-history premise from the source-facing route:
the exact history is derived internally from the generated source history and
local advance-safety proof.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_source_extensive_rationality_local_advance_safe_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining))
    (hadvance_safe :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        localModel hsource_extensive.2.1)
    (hstate_no_overshoot :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let exact_history :=
    (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_exact_drop_obligations
      localModel hsource_extensive hadvance_safe hstate_no_overshoot).2
  paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_drop_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le
    model exact_history hsource_extensive.2.2 initially_active completedRanks
    hcompleted_threshold_le

/--
Trace-rich local-advance-safe source-completion endpoint. The exact finite
`B*` trace in the conclusion is derived from the generated history and its
history-local advance-safety proof.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_source_extensive_rationality_local_advance_safe_ex_post_local_deviation_source_completion_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining))
    (hadvance_safe :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        localModel hsource_extensive.2.1)
    (hstate_no_overshoot :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let exact_history :=
    (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_exact_drop_obligations
      localModel hsource_extensive hadvance_safe hstate_no_overshoot).2
  paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_drop_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le
    model exact_history hsource_extensive.2.2 initially_active completedRanks
    hcompleted_threshold_le

/--
Payoff-facing local-advance-safe source-completion endpoint. The exact-drop
history needed for the finite terminal-record utility equality is derived from
the generated source history and local advance-safety.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_source_extensive_rationality_local_advance_safe_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_completed_threshold_le
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hsource_extensive :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining))
    (hadvance_safe :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        localModel hsource_extensive.2.1)
    (hstate_no_overshoot :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1))
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      let localModel :=
        paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel
      ∀ rank,
        rank ∈ completedRanks →
          paper_theorem8_bstar_threshold_bid
              localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
          model).base.strictModel
    (paper_theorem8_terminal_dropout_record_outcome finalState).utility
        ({ clickThroughRate := localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        localModel.value localModel.clickThroughRate
        (localModel.remaining + 1)).utility
        ({ clickThroughRate := localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        localModel.value rank :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
        model).base.strictModel
  let exact_history :=
    (paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_exact_drop_obligations
      localModel hsource_extensive hadvance_safe hstate_no_overshoot).2
  paper_theorem8_bstar_ranked_threshold_strict_ordered_exact_drop_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_completed_threshold_le
    model exact_history hsource_extensive.2.2 initially_active completedRanks
    hcompleted_threshold_le hrank

/--
Strict-ordered cold-start append schedules feed the ex-post local-deviation
source-completion endpoint directly. The threshold-sorted schedule data builds
the generated source history and local advance-safety evidence; Lean derives
the exact finite `B*` trace and completed-rank threshold reachability before
assembling the source-completion certificate.
-/
noncomputable def paper_theorem8_bstar_ranked_threshold_strict_ordered_cold_start_threshold_sorted_append_singleton_source_extensive_local_advance_safe_ex_post_source_completion_trace_full_completed_rank_terminal_record_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (completedRanks : Finset ℕ)
    (scheduledPrefix : List ℕ) (lastRank : ℕ)
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (scheduledPrefix ++ [lastRank]))
    (hnodup : (scheduledPrefix ++ [lastRank]).Nodup)
    (hunscheduled_last :
      ∀ rank,
        rank ∉ scheduledPrefix ++ [lastRank] →
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              lastRank <
            paper_theorem8_bstar_threshold_bid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledPrefix ++ [lastRank]) :=
  paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
    model completedRanks scheduledPrefix lastRank hthreshold_sorted hnodup
    hunscheduled_last hsubset

/--
Cold-start source-extensive local-safety all-terminal theorem. The EOS
cold-start state discharges initial no-overshoot and initial activity, leaving
only source-extensive rationality, history-local advance safety, and final
all-ranks inactivity.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_local_advance_safe_trace_all_terminal_vcg_conclusion
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      (fun rank => by rfl) hno_active

/--
Belief-explicit cold-start counterpart of the local-safety all-terminal source
theorem.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hsource_extensive.2.1)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hsource_extensive hadvance_safe
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      (fun rank => by rfl) hno_active

/--
Cold-start generated-history local-safety all-terminal theorem. The named
strategy's source sequential rationality is supplied internally.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_trace_all_terminal_vcg_conclusion
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
  simpa using
    paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_local_advance_safe_trace_all_terminal_vcg_conclusion
      model hvalue_nonneg hclick_mono hsource_extensive hadvance_safe
      hno_active

/--
Belief-explicit cold-start generated-history local-safety all-terminal theorem.
-/
theorem paper_theorem8_bstar_ranked_threshold_cold_start_strategy_history_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
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
      PaperTheorem8BStarRankedThresholdStrategyHistoryAdvanceSafe
        model hhist)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let htrace :=
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_history_advance_safe
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
  simpa using
    paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_local_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hvalue_nonneg hclick_mono hsource_extensive hadvance_safe
      hno_active

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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
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
      paper_theorem8_bstar_ranked_threshold_strategy_history_to_source_extensive_rationality
        model hhist terminal
  simpa using
    paper_theorem8_bstar_ranked_threshold_cold_start_source_extensive_rationality_advance_safe_belief_trace_all_terminal_vcg_conclusion
      model hvalue_nonneg hclick_mono hsource_extensive hadvance_safe
      hno_active

end Auction
end EconCSLib
