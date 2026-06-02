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

end Auction
end EconCSLib
