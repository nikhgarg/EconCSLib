import EOS07GSP.MainTheorems

/-!
# Proof Interface: Internet Advertising and the Generalized Second-Price Auction

This file preserves the implementation-facing Lean surface for Edelman,
Ostrovsky, and Schwarz, *Internet Advertising and the Generalized Second-Price
Auction*.  The compact human-review surface is `PaperInterface.lean`; this file
retains the larger endpoint ledger used by downstream wrappers and older
documentation.
-/

namespace EOS07GSP
namespace PaperInterface

open EconCSLib.Auction

noncomputable section

/-! ## Position-Auction Definitions -/

/-- The paper's GSP truthfulness target for the concrete three-bidder/two-slot witness. -/
abbrev gspDominantStrategyTruthful : Prop :=
  PositionMechanism.TruthfulDominantStrategy
    gspCounterexampleEnvironment gsp3TwoSlotMechanism

/-- Locally envy-free outcome predicate used for EOS Definition 4. -/
abbrev locallyEnvyFree {Bidder Slot : Type*}
    (environment : PositionEnvironment Slot)
    (values : Bidder → ℝ)
    (outcome : PositionOutcome Bidder Slot) : Prop :=
  outcome.SlotEnvyFree environment values

/-- Stable assignment predicate used by the paper's stable-assignment bridge. -/
abbrev stableAssignment {Bidder Slot : Type*}
    (environment : PositionEnvironment Slot)
    (values : Bidder → ℝ)
    (outcome : PositionOutcome Bidder Slot) : Prop :=
  outcome.StableAssignment environment values

/-- The ranked `B*` bid displayed in Theorem 7. -/
abbrev theorem7BStarBid
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (rank : ℕ) : ℝ :=
  paper_theorem7_bstar_bid value vcgTotalPayment clickThroughRate rank

/-- The finite `B*` threshold bid displayed in Theorem 8. -/
abbrev theorem8BStarThresholdBid
    (value clickThroughRate : ℕ → ℝ) (remaining rank : ℕ) : ℝ :=
  paper_theorem8_bstar_threshold_bid value clickThroughRate remaining rank

/--
The source-timing premise needed by the remaining Theorem 8 generalized-English
source proof: every realized new dropout under the named finite `B*` strategy
occurs without overshooting that rank's finite `B*` threshold.
-/
abbrev theorem8RealizedNewDropoutNoOvershootStatement
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate) :
    Prop :=
  paper_theorem8_bstar_ranked_threshold_realized_new_dropout_no_overshoot_statement
    model

/--
The continuation finite `B*` bid is weakly below the current finite `B*`
threshold under the ordered assumptions used by Theorem 8.
-/
theorem theorem8BStarContinuationThresholdLeCurrent_of_ordered_tail
    {value clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_mono : ∀ i, value (i + 1) ≤ value i)
    (hclick_pos : ∀ i, 0 < clickThroughRate i)
    (hclick_mono : ∀ i, clickThroughRate (i + 1) ≤ clickThroughRate i)
    (remaining rank : ℕ) :
    theorem8BStarThresholdBid value clickThroughRate remaining (rank + 2) ≤
      theorem8BStarThresholdBid value clickThroughRate (remaining + 1) (rank + 1) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_continuation_threshold_le_current_threshold_of_ordered_tail
      hvalue_nonneg hvalue_mono hclick_pos hclick_mono remaining rank

/--
For any two displayed ranks, the cold-start exact-drop pair can be checked in
one of the two threshold orders. This is the small-schedule review helper to
use when rank order itself does not decide the finite `B*` threshold order.
-/
theorem theorem8_cold_start_pair_clock_sorted_in_some_order
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ) :
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        [rank, nextRank] ∨
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        [nextRank, rank] := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_pair_or_swap
      model rank nextRank

/--
Existential two-rank cold-start schedule helper. Given two distinct ranks, this
returns either `[rank, nextRank]` or `[nextRank, rank]` as a no-duplicate
clock-sorted exact-drop schedule.
-/
theorem theorem8_cold_start_pair_clock_sorted_schedule_exists
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hne : rank ≠ nextRank) :
    ∃ scheduledRanks : List ℕ,
      (scheduledRanks = [rank, nextRank] ∨
        scheduledRanks = [nextRank, rank]) ∧
        scheduledRanks.Nodup ∧
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
            (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
              model)
            paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
            scheduledRanks := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_schedule_exists
      model rank nextRank hne

/--
Two-rank cold-start schedule package. If every unscheduled rank's threshold is
above the larger of the two displayed thresholds, Lean chooses the sorted order
and returns the no-duplicate schedule together with the terminality check used
by finite terminal-record endpoints.
-/
theorem theorem8_cold_start_pair_clock_sorted_terminality_schedule_exists
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hne : rank ≠ nextRank)
    (hunscheduled_after_max :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            max
                (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                    model)
                  rank)
                (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                    model)
                  nextRank) <
              theorem8BStarThresholdBid
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).value
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).clickThroughRate
                ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).remaining + 1)
                (otherRank + 1)) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    ∃ scheduledRanks : List ℕ,
      (scheduledRanks = [rank, nextRank] ∨
        scheduledRanks = [nextRank, rank]) ∧
        scheduledRanks.Nodup ∧
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
            localModel
            paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
            scheduledRanks ∧
            ∀ otherRank,
              otherRank ∉ scheduledRanks →
                (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
                  localModel
                  paper_theorem8_bstar_ranked_threshold_cold_start_state
                  scheduledRanks).clockPrice <
                  theorem8BStarThresholdBid
                    localModel.value localModel.clickThroughRate
                    (localModel.remaining + 1) (otherRank + 1) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_terminality_schedule_exists
      model rank nextRank hne hunscheduled_after_max

/-- Terminal-record source-shaped checker for Theorem 8. -/
abbrev terminalRecordSourceGame
    (terminal : PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate) :=
  paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game
    terminal

/--
Terminal-record source-extensive checker for Theorem 8.  Unlike the
source-shaped checker, its PBE predicate includes the concrete generated
history and terminality proof for the audited terminal state.
-/
abbrev terminalRecordSourceExtensiveGame
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate) :=
  paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
    terminal

/--
Belief-explicit terminal-record source-extensive checker for Theorem 8. The
belief object carries the generated source history and terminality proof, and
belief consistency checks that this history belongs to the strategy under
review.
-/
abbrev terminalRecordBeliefSourceExtensiveGame
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate) :=
  paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
    terminal

/-- Canonical belief used by the belief-explicit source-extensive checker. -/
noncomputable abbrev terminalRecordBeliefSourceExtensiveNamedBelief
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate) :=
  paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_named_belief
    terminal

/--
Source-shaped checker for Theorem 8. Its sequential-rationality predicate is
the reachable/off-path source target used by the generalized-English proof
plan, while consistency and the outcome map are compact audit scaffolding.
-/
abbrev sourceSequentialGame
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :=
  paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game
    model initialState

/--
Displayed finite completed-rank conclusion for the terminal-record checker:
the rank gets its rank slot, pays the finite `B*` threshold, matches VCG-tail
accounting, and pays within `[0, value]`.
-/
abbrev completedRankPaperFormula
    (terminal : PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate)
    {Belief : Type*}
    (G :
      PaperTheorem8GeneralizedEnglishDynamicGame
        ℕ ℕ (PaperTheorem8GeneralizedEnglishStrategy ℕ) Belief)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ)
    (rank : ℕ) : Prop :=
  (G.outcomeOf strategy).slotOf rank = some rank ∧
    (G.outcomeOf strategy).paymentPerClick rank =
      theorem8BStarThresholdBid
        terminal.localModel.value terminal.localModel.clickThroughRate
        (terminal.localModel.remaining + 1) (rank + 1) ∧
      terminal.localModel.clickThroughRate rank *
          (G.outcomeOf strategy).paymentPerClick rank =
        paper_theorem7_ranked_vcg_tail_payment
          terminal.localModel.value terminal.localModel.clickThroughRate rank
          (terminal.localModel.remaining + 1) ∧
        0 ≤ (G.outcomeOf strategy).paymentPerClick rank ∧
          (G.outcomeOf strategy).paymentPerClick rank ≤
            terminal.localModel.value rank

/--
Displayed finite completed-rank conclusion for terminal dropout records:
the terminal record outcome assigns the rank slot, finite `B*` threshold
payment, VCG-tail accounting, and payment bounds.
-/
abbrev completedRankTerminalRecordFormula
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (rank : ℕ) : Prop :=
  (paper_theorem8_terminal_dropout_record_outcome
    terminal.finalState).slotOf rank = some rank ∧
    (paper_theorem8_terminal_dropout_record_outcome
      terminal.finalState).paymentPerClick rank =
      theorem8BStarThresholdBid
        terminal.localModel.value terminal.localModel.clickThroughRate
        (terminal.localModel.remaining + 1) (rank + 1) ∧
      terminal.localModel.clickThroughRate rank *
          (paper_theorem8_terminal_dropout_record_outcome
            terminal.finalState).paymentPerClick rank =
        paper_theorem7_ranked_vcg_tail_payment
          terminal.localModel.value terminal.localModel.clickThroughRate rank
          (terminal.localModel.remaining + 1) ∧
        0 ≤
          (paper_theorem8_terminal_dropout_record_outcome
            terminal.finalState).paymentPerClick rank ∧
          (paper_theorem8_terminal_dropout_record_outcome
            terminal.finalState).paymentPerClick rank ≤
            terminal.localModel.value rank

/-! ## Theorem 8 Proof-Line Payoff Comparisons -/

/--
Theorem 8 Step 2 payoff comparison: if the clock is below the indifference
price `q`, waiting for the higher slot is strictly better than dropping now.
-/
theorem theorem8_source_step2_waiting_before_q_strictly_better
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hclock_lt :
      state.clockPrice <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank) :
    clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) <
      clickThroughRate rank * (value (rank + 1) - state.clockPrice) := by
  exact
    paper_theorem8_source_step2_waiting_before_q_strictly_better
      hclick_pos hclock_lt

/--
Theorem 8 Step 1 payoff comparison: if the clock is above the indifference
price `q`, dropping now is strictly better than waiting for the higher slot.
-/
theorem theorem8_source_step1_dropping_after_q_strictly_better
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hthreshold_lt :
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank <
        state.clockPrice) :
    clickThroughRate rank * (value (rank + 1) - state.clockPrice) <
      clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) := by
  exact
    paper_theorem8_source_step1_dropping_after_q_strictly_better
      hclick_pos hthreshold_lt

/-- The indifference price `q` lies in the weak interval between the last
dropout price and the next bidder value under the paper's weak click-rate
conditions. -/
theorem theorem8_source_q_mem_interval
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_nonneg : 0 ≤ clickThroughRate (rank + 1))
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hlastDropout_le : lastDropout rank ≤ value (rank + 1)) :
    lastDropout rank ≤
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank ∧
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank ≤ value (rank + 1) := by
  exact
    paper_theorem8_source_q_mem_interval
      hclick_pos hcurrent_nonneg hcurrent_le hlastDropout_le

/-- The indifference price `q` lies strictly between the last dropout price and
the next bidder value under the paper's strict click-rate conditions. -/
theorem theorem8_source_q_strict_mem_interval
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_pos : 0 < clickThroughRate (rank + 1))
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hlastDropout_lt : lastDropout rank < value (rank + 1)) :
    lastDropout rank <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank ∧
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank < value (rank + 1) := by
  exact
    paper_theorem8_source_q_strict_mem_interval
      hclick_pos hcurrent_pos hcurrent_lt hlastDropout_lt

/-- Increasing the next bidder value strictly increases the indifference price
`q` under the paper's strict click-rate condition. -/
theorem theorem8_source_q_strict_mono_value
    {clickThroughRate lastDropout value value' : ℕ → ℝ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hvalue_lt : value (rank + 1) < value' (rank + 1)) :
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank <
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value' rank := by
  exact
    paper_theorem8_source_q_strict_mono_value
      hclick_pos hcurrent_lt hvalue_lt

/-- The indifference price `q` is continuous in the lower bidder's value when
the history and other values are fixed. -/
theorem theorem8_source_q_continuous_value
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) :
    Continuous
      (fun bidderValue : ℝ =>
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout
          (Function.update value (rank + 1) bidderValue)
          rank) := by
  exact
    paper_theorem8_source_q_continuous_value
      clickThroughRate lastDropout value rank

/-- Empty-history convention for `q`: if the previous dropout price is zero,
the formula reduces to the displayed value-weighted term. -/
theorem theorem8_source_q_empty_history_eq
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hlast : lastDropout rank = 0) :
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank =
      (1 - clickThroughRate (rank + 1) / clickThroughRate rank) *
        value (rank + 1) := by
  exact paper_theorem8_source_q_empty_history_eq hlast

/-- The affine form of the indifference price `q` between the lower bidder's
value and the previous dropout price. -/
theorem theorem8_source_q_affine_eq
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ} :
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank =
      (1 - clickThroughRate (rank + 1) / clickThroughRate rank) *
          value (rank + 1) +
        (clickThroughRate (rank + 1) / clickThroughRate rank) *
          lastDropout rank := by
  exact paper_theorem8_source_q_affine_eq

/-- Under strict adjacent click-through rates, `q` identifies the lower
bidder's value when history and other values are fixed. -/
theorem theorem8_source_q_injective_value
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank) :
    Function.Injective
      (fun bidderValue : ℝ =>
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout
          (Function.update value (rank + 1) bidderValue)
          rank) := by
  exact
    paper_theorem8_source_q_injective_value
      clickThroughRate lastDropout value rank hclick_pos hcurrent_lt

/-- Increasing the previous dropout price weakly increases the next
indifference price `q`. -/
theorem theorem8_source_q_mono_lastDropout
    {clickThroughRate lastDropout lastDropout' value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_nonneg : 0 ≤ clickThroughRate (rank + 1))
    (hlastDropout_le : lastDropout rank ≤ lastDropout' rank) :
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ≤
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout' value rank := by
  exact
    paper_theorem8_source_q_mono_lastDropout
      hclick_pos hcurrent_nonneg hlastDropout_le

/-- With positive lower click-through rate, strictly increasing the previous
dropout price strictly increases the next indifference price `q`. -/
theorem theorem8_source_q_strict_mono_lastDropout
    {clickThroughRate lastDropout lastDropout' value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_pos : 0 < clickThroughRate (rank + 1))
    (hlastDropout_lt : lastDropout rank < lastDropout' rank) :
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank <
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout' value rank := by
  exact
    paper_theorem8_source_q_strict_mono_lastDropout
      hclick_pos hcurrent_pos hlastDropout_lt

/-! ## Source Theorems -/

/-- GSP is not dominant-strategy truthful, witnessed by the paper's small example. -/
theorem gsp_not_dominant_strategy_truthful :
    ¬ gspDominantStrategyTruthful := by
  exact paper_sorted_gsp_three_bidder_two_slot_not_truthful

/-- Running example: truthful GSP revenue is `1000`, VCG revenue is `800`. -/
theorem running_example_revenue_comparison :
    paper_eos_running_example_clickThroughRate 0 *
          paper_eos_running_example_value 1 +
        paper_eos_running_example_clickThroughRate 1 *
          paper_eos_running_example_value 2 = 1000 ∧
      paper_theorem7_ranked_vcg_tail_payment
            paper_eos_running_example_value
            paper_eos_running_example_clickThroughRate 0 2 +
          paper_theorem7_ranked_vcg_tail_payment
            paper_eos_running_example_value
            paper_eos_running_example_clickThroughRate 1 1 = 800 := by
  exact
    ⟨paper_eos_running_example_truthful_gsp_revenue_eq,
      paper_eos_running_example_vcg_revenue_eq⟩

/--
Remark 1 generic same-bid payment comparison: under weakly decreasing
nonnegative values and nonnegative click-through rates, the VCG per-click
charge at a rank is weakly below the truthful GSP next-bid payment `v_{i+1}`.
-/
theorem remark1_truthful_gsp_payment_weakly_dominates_vcg_per_click
    {value clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_mono : ∀ i, value (i + 1) ≤ value i)
    (hclick_nonneg : ∀ i, 0 ≤ clickThroughRate i)
    {rank remaining : ℕ}
    (hclick_pos : 0 < clickThroughRate rank) :
    paper_theorem7_ranked_vcg_tail_payment
        value clickThroughRate rank remaining / clickThroughRate rank ≤
      value (rank + 1) := by
  exact
    paper_remark1_ranked_vcg_per_click_le_truthful_gsp_payment
      hvalue_nonneg hvalue_mono hclick_nonneg hclick_pos

/--
Remark 2: VCG-style position mechanisms are dominant-strategy truthful. The
certificate records welfare maximization plus the standard externality-tax
utility identity, with the tax independent of the bidder's own report.
-/
theorem remark2_vcg_position_mechanism_truthful
    {Bidder Slot : Type*} [Fintype Bidder] [DecidableEq Bidder]
    {E : PositionEnvironment Slot} {M : PositionMechanism Bidder Slot}
    (C : PositionMechanism.VCGDominantStrategyCertificate E M) :
    PositionMechanism.TruthfulDominantStrategy E M := by
  exact paper_remark2_vcg_position_mechanism_truthful C

/-- Running example: truthful bidding is a Nash equilibrium of the GSP mechanism. -/
theorem running_example_truthful_gsp_is_nash :
    PositionMechanism.IsNashEquilibrium
      paper_eos_running_example_environment
      gsp3TwoSlotMechanism
      paper_eos_running_example_values3
      paper_eos_running_example_values3 := by
  exact paper_eos_running_example_truthful_gsp_is_nash

/--
Theorem 7 paper-facing endpoint: under ordered finite-tail assumptions and
nonnegative values, the constructed ranked `B*` outcome is no-positive-transfer,
locally envy-free, stable, VCG-equivalent, and revenue-minimal among
same-assignment locally envy-free no-positive-transfer comparison outcomes.
-/
theorem theorem7_ranked_bstar_vcg_equivalent_locally_envy_free
    {n : ℕ}
    (model :
      PaperTheorem7OrderedRankedCanonicalTailComparisonPaymentCertificate n)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i) :
    ∃ O : PositionOutcome (Fin n) (Fin n),
      paper_position_no_positive_transfers O ∧
        O.SlotEnvyFree
          (paper_theorem7_ranked_environment model.clickThroughRate)
          (fun i : Fin n => model.value i.val) ∧
        O.StableAssignment
          (paper_theorem7_ranked_environment model.clickThroughRate)
          (fun i : Fin n => model.value i.val) ∧
        (∀ i, O.slotOf i = model.vcgOutcome.slotOf i) ∧
        (∀ i, O.paymentPerClick i = model.vcgOutcome.paymentPerClick i) ∧
        ∀ other : PositionOutcome (Fin n) (Fin n),
          other.FeasibleAssignment →
          other.IndividuallyRational
            (paper_theorem7_ranked_environment model.clickThroughRate)
            (fun i : Fin n => model.value i.val) →
          other.SlotEnvyFree
            (paper_theorem7_ranked_environment model.clickThroughRate)
            (fun i : Fin n => model.value i.val) →
            (∀ i, O.slotOf i = other.slotOf i) →
              paper_position_no_positive_transfers other →
                O.revenue
                    (paper_theorem7_ranked_environment model.clickThroughRate) ≤
                  other.revenue
                    (paper_theorem7_ranked_environment model.clickThroughRate) := by
  exact
    paper_theorem7_ordered_ranked_canonical_tail_no_positive_transfer_paper_conclusion
      model hvalue_nonneg

/--
The source-shaped checker's PBE predicate is exactly the reachable/off-path
source sequential-rationality target.
-/
theorem theorem8_source_sequential_pbe_iff_source_target
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (sourceSequentialGame model initialState).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
        model.clickThroughRate model.value model.remaining initialState
        strategy := by
  simpa [sourceSequentialGame] using
    paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_source_sequential
      model initialState strategy

/--
The source-shaped checker recognizes exactly the named finite `B*`
ranked-threshold strategy as PBE.
-/
theorem theorem8_source_sequential_pbe_iff_named_strategy
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (sourceSequentialGame model initialState).PerfectBayesianEquilibrium
        strategy ↔
      strategy =
        paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining := by
  simpa [sourceSequentialGame] using
    paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_named_strategy
      model initialState strategy

/--
The source-shaped checker's PBE predicate in one-step best-response plus
at-threshold tie-break form.
-/
theorem theorem8_source_sequential_pbe_iff_one_step_best_response_and_drop_at_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (sourceSequentialGame model initialState).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
          model.clickThroughRate model.value model.remaining strategy ∧
        paper_theorem8_bstar_ranked_threshold_drop_at_threshold_statement
          model.clickThroughRate model.value model.remaining strategy := by
  simpa [sourceSequentialGame] using
    paper_theorem8_bstar_ranked_threshold_source_sequential_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold
      model initialState strategy

/--
One-stop source-obligation endpoint for the full Theorem 8 conclusion.  Supply
the concrete belief-consistency proof, the reachable/off-path
sequential-rationality iff, generated PBE histories, no-overshoot dropout
timing, and terminal-record outcome/VCG identification; Lean returns the
unique-PBE full conclusion.
-/
theorem theorem8_source_iff_histories_no_overshoot_full_conclusion
    {Belief : Type*}
    (integrated :
      PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicCertificate
        Belief)
    (concrete_belief_consistency :
      integrated.dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          integrated.dynamic.base.strictModel.value
          integrated.dynamic.base.strictModel.clickThroughRate
          integrated.dynamic.base.strictModel.remaining)
        integrated.dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        integrated.dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            integrated.dynamic.base.strictModel.clickThroughRate
            integrated.dynamic.base.strictModel.value
            integrated.dynamic.base.strictModel.remaining
            integrated.terminal.initialState
            strategy)
    (hhist :
      ∀ strategy,
        integrated.dynamic.base.game.PerfectBayesianEquilibrium strategy →
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
            strategy
            integrated.terminal.initialState
            integrated.terminal.finalState)
    (hno_overshoot :
      ∀ strategy,
        integrated.dynamic.base.game.PerfectBayesianEquilibrium strategy →
          ∀ state rank,
            state.IsActive rank →
              strategy state rank →
                state.clockPrice ≤
                  theorem8BStarThresholdBid
                    integrated.dynamic.base.strictModel.value
                    integrated.dynamic.base.strictModel.clickThroughRate
                    (integrated.dynamic.base.strictModel.remaining + 1)
                    (rank + 1))
    (hinitial_active :
      ∀ rank, integrated.terminal.initialState.IsActive rank)
    (hno_active :
      ∀ rank, ¬ integrated.terminal.finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        integrated.dynamic.base.game.PerfectBayesianEquilibrium strategy →
          integrated.dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome
              integrated.terminal.finalState)
    (hvcg :
      integrated.dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          integrated.dynamic.base.strictModel.value
          integrated.dynamic.base.strictModel.clickThroughRate
          (integrated.dynamic.base.strictModel.remaining + 1)) :
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      integrated.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_iff_histories_no_overshoot_exists_unique_pbe_with_full_conclusion
      integrated concrete_belief_consistency
      sequential_rationality_iff_source_sequential hhist
      (by
        intro strategy hpbe state rank hactive hdrop
        simpa [theorem8BStarThresholdBid] using
          hno_overshoot strategy hpbe state rank hactive hdrop)
      hinitial_active hno_active houtcome hvcg

/--
No-overshoot terminal-dynamic source endpoint for the full Theorem 8
conclusion.  Compared with the general source-history wrapper above, the
annotated terminal history supplies the generated-history and no-overshoot
record evidence internally.
-/
theorem theorem8_no_overshoot_terminal_dynamic_source_iff_full_conclusion
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (concrete_belief_consistency :
      cert.dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          cert.dynamic.base.strictModel.remaining)
        cert.dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        cert.dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            cert.dynamic.base.strictModel.clickThroughRate
            cert.dynamic.base.strictModel.value
            cert.dynamic.base.strictModel.remaining
            cert.terminal.initialState
            strategy)
    (hno_active : ∀ rank, ¬ cert.terminal.finalState.IsActive rank)
    (houtcome :
      ∀ strategy,
        cert.dynamic.base.game.PerfectBayesianEquilibrium strategy →
          cert.dynamic.base.game.outcomeOf strategy =
            paper_theorem8_terminal_dropout_record_outcome
              cert.terminal.finalState)
    (hvcg :
      cert.dynamic.base.game.vcgOutcome =
        paper_theorem8_bstar_ranked_threshold_outcome
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          (cert.dynamic.base.strictModel.remaining + 1)) :
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion
      cert concrete_belief_consistency
      sequential_rationality_iff_source_sequential hno_active houtcome hvcg

/--
Completed-rank no-overshoot terminal-dynamic source endpoint.  The terminal
clock cutoff proves completed-rank inactivity, so the source proof only needs
belief consistency and the reachable/off-path sequential-rationality iff.
-/
theorem theorem8_no_overshoot_terminal_dynamic_source_iff_completed_threshold_conclusion
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (concrete_belief_consistency :
      cert.dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          cert.dynamic.base.strictModel.remaining)
        cert.dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        cert.dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            cert.dynamic.base.strictModel.clickThroughRate
            cert.dynamic.base.strictModel.value
            cert.dynamic.base.strictModel.remaining
            cert.terminal.initialState
            strategy)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              cert.terminal.localModel.value cert.terminal.localModel.clickThroughRate
              (cert.terminal.localModel.remaining + 1) (rank + 1) ≤
            cert.terminal.finalState.clockPrice) :
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
                  theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      cert concrete_belief_consistency
      sequential_rationality_iff_source_sequential completedRanks
      (by
        intro rank hrank
        exact
          (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_inactive_iff_threshold_le_clock
            cert.terminal rank).mpr
            (by
              simpa [theorem8BStarThresholdBid] using
                hcompleted_threshold_le rank hrank))

/--
Completed-rank no-overshoot terminal-dynamic source endpoint with the completed
set supplied directly as terminal-inactive ranks.
-/
theorem theorem8_no_overshoot_terminal_dynamic_source_iff_completed_rank_conclusion
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (concrete_belief_consistency :
      cert.dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          cert.dynamic.base.strictModel.remaining)
        cert.dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        cert.dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            cert.dynamic.base.strictModel.clickThroughRate
            cert.dynamic.base.strictModel.value
            cert.dynamic.base.strictModel.remaining
            cert.terminal.initialState
            strategy)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ cert.terminal.finalState.IsActive rank) :
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
                  theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      cert concrete_belief_consistency
      sequential_rationality_iff_source_sequential completedRanks
      inactive_on_completed

/--
Payoff-facing completed-rank form of the no-overshoot terminal-dynamic source
endpoint.
-/
theorem theorem8_no_overshoot_terminal_dynamic_source_iff_utility_eq_bstar_of_completed_threshold
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (concrete_belief_consistency :
      cert.dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          cert.dynamic.base.strictModel.remaining)
        cert.dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        cert.dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            cert.dynamic.base.strictModel.clickThroughRate
            cert.dynamic.base.strictModel.value
            cert.dynamic.base.strictModel.remaining
            cert.terminal.initialState
            strategy)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              cert.terminal.localModel.value cert.terminal.localModel.clickThroughRate
              (cert.terminal.localModel.remaining + 1) (rank + 1) ≤
            cert.terminal.finalState.clockPrice)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    (paper_theorem8_terminal_dropout_record_outcome
        cert.terminal.finalState).utility
        ({ clickThroughRate := cert.terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        cert.terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        cert.terminal.localModel.value cert.terminal.localModel.clickThroughRate
        (cert.terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate := cert.terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        cert.terminal.localModel.value rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_terminal_record_utility_eq_bstar_of_mem
      cert concrete_belief_consistency
      sequential_rationality_iff_source_sequential completedRanks
      (by
        intro rank hrank
        exact
          (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_inactive_iff_threshold_le_clock
            cert.terminal rank).mpr
            (by
              simpa [theorem8BStarThresholdBid] using
                hcompleted_threshold_le rank hrank))
      hrank

/--
Payoff-facing completed-rank form of the no-overshoot terminal-dynamic source
endpoint from direct terminal inactivity on completed ranks.
-/
theorem theorem8_no_overshoot_terminal_dynamic_source_iff_utility_eq_bstar_of_completed_rank
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (concrete_belief_consistency :
      cert.dynamic.base.game.isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          cert.dynamic.base.strictModel.remaining)
        cert.dynamic.base.belief)
    (sequential_rationality_iff_source_sequential :
      ∀ strategy belief,
        cert.dynamic.base.game.isSequentiallyRational strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement
            cert.dynamic.base.strictModel.clickThroughRate
            cert.dynamic.base.strictModel.value
            cert.dynamic.base.strictModel.remaining
            cert.terminal.initialState
            strategy)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ cert.terminal.finalState.IsActive rank)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    (paper_theorem8_terminal_dropout_record_outcome
        cert.terminal.finalState).utility
        ({ clickThroughRate := cert.terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        cert.terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        cert.terminal.localModel.value cert.terminal.localModel.clickThroughRate
        (cert.terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate := cert.terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        cert.terminal.localModel.value rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_terminal_record_utility_eq_bstar_of_mem
      cert concrete_belief_consistency
      sequential_rationality_iff_source_sequential completedRanks
      inactive_on_completed hrank

/--
Clock-disciplined source-iff endpoint for the full Theorem 8 conclusion.  The
clock-disciplined trace is converted internally to the no-overshoot
terminal/dynamic certificate, while the source proof supplies only belief
consistency, the reachable/off-path sequential-rationality iff, all-terminal
inactivity, and the outcome/VCG identifications.
-/
theorem theorem8_clock_disciplined_terminal_history_source_iff_full_conclusion
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
            theorem8BStarThresholdBid
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
        dynamic hhist
        (by
          intro rank hactive
          simpa [theorem8BStarThresholdBid] using
            hstate_no_overshoot rank hactive)
        terminal initially_active
    let integrated :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          integrated strategy := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_exists_unique_pbe_with_full_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist
        (by
          intro rank hactive
          simpa [theorem8BStarThresholdBid] using
            hstate_no_overshoot rank hactive)
        terminal initially_active)
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
Clock-disciplined source-iff endpoint with completed-rank terminal-record
formulas.  This is the finite-rank version of the previous wrapper: the
clock-disciplined trace builds the no-overshoot certificate internally, and
the terminal clock cutoff proves the completed-rank inactivity needed for the
displayed slot/payment/VCG-tail formulas.
-/
theorem theorem8_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion
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
            theorem8BStarThresholdBid
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
          theorem8BStarThresholdBid
              dynamic.base.strictModel.value dynamic.base.strictModel.clickThroughRate
              (dynamic.base.strictModel.remaining + 1) (rank + 1) ≤
            finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist
        (by
          intro rank hactive
          simpa [theorem8BStarThresholdBid] using
            hstate_no_overshoot rank hactive)
        terminal initially_active
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
                  theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_source_sequential_rationality_finite_exact_history_exists_unique_pbe_with_terminal_record_conclusion
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist
        (by
          intro rank hactive
          simpa [theorem8BStarThresholdBid] using
            hstate_no_overshoot rank hactive)
        terminal initially_active)
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
              dynamic hhist
              (by
                intro rank hactive
                simpa [theorem8BStarThresholdBid] using
                  hstate_no_overshoot rank hactive)
              terminal initially_active).terminal
            rank).mpr
            (by
              simpa [theorem8BStarThresholdBid,
                paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history,
                paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
                hcompleted_threshold_le rank hrank))

/--
Cold-start source-iff endpoint for the full Theorem 8 conclusion. The
clock-disciplined trace starts at the cold-start state, so the initial
no-overshoot and initial-activity premises are derived internally.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_iff_full_conclusion
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
  simpa [theorem8BStarThresholdBid,
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history] using
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
Cold-start source-iff endpoint with completed-rank terminal-record formulas.
This is the completed-rank version of the previous wrapper; the terminal clock
threshold premise proves completed-rank inactivity.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_iff_completed_threshold_conclusion
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
          theorem8BStarThresholdBid
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
                  theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid,
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history] using
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
              simpa [theorem8BStarThresholdBid,
                paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history,
                paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict] using
                hcompleted_threshold_le rank hrank))

/--
The source-extensive rationality target splits into exactly the local-deviation
sequential-rationality proof, the generated history, and terminality.
-/
theorem theorem8_source_extensive_rationality_iff_local_deviation_history_terminal
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model initialState finalState strategy ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
          model.clickThroughRate model.value model.remaining strategy ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
          strategy initialState finalState ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
            strategy finalState := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_iff_local_deviation_history_terminal
      model initialState finalState strategy

/--
The source-extensive terminal-record checker's PBE predicate is exactly local
deviation plus the generated history and terminality obligations.
-/
theorem theorem8_source_extensive_pbe_iff_local_deviation_history_terminal
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
          strategy terminal.initialState terminal.finalState ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
            strategy terminal.finalState := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_local_deviation_history_terminal
      terminal strategy

/--
Belief-explicit source-extensive PBE: the belief carries the generated source
history and terminality proof, while sequential rationality remains the
reachable/off-path payoff target.
-/
theorem theorem8_belief_source_extensive_pbe_iff_source_extensive
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        terminal.localModel terminal.initialState terminal.finalState
        strategy := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_source_extensive
      terminal strategy

/--
The canonical source-extensive belief is consistent with the named finite
`B*` strategy.
-/
theorem theorem8_belief_source_extensive_named_belief_consistent
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate) :
    (terminalRecordBeliefSourceExtensiveGame terminal).isConsistentBelief
        (paper_theorem8_bstar_ranked_threshold_strategy
          terminal.localModel.value terminal.localModel.clickThroughRate
          terminal.localModel.remaining)
        (terminalRecordBeliefSourceExtensiveNamedBelief terminal) := by
  simpa [terminalRecordBeliefSourceExtensiveGame,
    terminalRecordBeliefSourceExtensiveNamedBelief] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_named_belief_consistent
      terminal

/--
The named finite `B*` strategy is source-sequentially rational under the
canonical source-extensive belief.
-/
theorem theorem8_belief_source_extensive_named_belief_sequentially_rational
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate) :
    (terminalRecordBeliefSourceExtensiveGame terminal).isSequentiallyRational
        (paper_theorem8_bstar_ranked_threshold_strategy
          terminal.localModel.value terminal.localModel.clickThroughRate
          terminal.localModel.remaining)
        (terminalRecordBeliefSourceExtensiveNamedBelief terminal) := by
  simpa [terminalRecordBeliefSourceExtensiveGame,
    terminalRecordBeliefSourceExtensiveNamedBelief] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_named_belief_sequentially_rational
      terminal

/--
The canonical source-extensive belief is an explicit PBE witness for the named
finite `B*` strategy.
-/
theorem theorem8_belief_source_extensive_named_strategy_pbe_from_named_belief
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate) :
    (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        (paper_theorem8_bstar_ranked_threshold_strategy
          terminal.localModel.value terminal.localModel.clickThroughRate
          terminal.localModel.remaining) := by
  simpa [terminalRecordBeliefSourceExtensiveGame,
    terminalRecordBeliefSourceExtensiveNamedBelief] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_named_strategy_pbe_from_named_belief
      terminal

/--
The belief-explicit source-extensive checker reduces to local deviation plus
generated history and terminality.
-/
theorem theorem8_belief_source_extensive_pbe_iff_local_deviation_history_terminal
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
          strategy terminal.initialState terminal.finalState ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
            strategy terminal.finalState := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_local_deviation_history_terminal
      terminal strategy

/--
For an audited no-overshoot terminal certificate, the source-extensive checker
accepts exactly the locally deviation-rational strategies.
-/
theorem theorem8_source_extensive_pbe_iff_local_deviation
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
        terminal.localModel.clickThroughRate terminal.localModel.value
        terminal.localModel.remaining strategy := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_local_deviation
      terminal strategy

/--
For an audited no-overshoot terminal certificate, the belief-explicit
source-extensive checker accepts exactly the locally deviation-rational
strategies.
-/
theorem theorem8_belief_source_extensive_pbe_iff_local_deviation
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
        terminal.localModel.clickThroughRate terminal.localModel.value
        terminal.localModel.remaining strategy := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_local_deviation
      terminal strategy

/--
The belief-explicit source-extensive checker has exactly the named finite `B*`
ranked-threshold strategy as PBE.
-/
theorem theorem8_belief_source_extensive_pbe_iff_named_strategy
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      strategy =
        paper_theorem8_bstar_ranked_threshold_strategy
          terminal.localModel.value terminal.localModel.clickThroughRate
          terminal.localModel.remaining := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_named_strategy
      terminal strategy

/--
The belief-explicit source-extensive PBE check written in the paper's one-step
best-response and at-threshold tie-break obligations.
-/
theorem theorem8_belief_source_extensive_pbe_iff_one_step_best_response_and_drop_at_threshold
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy ∧
        paper_theorem8_bstar_ranked_threshold_drop_at_threshold_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold
      terminal strategy

/--
Every belief-explicit source-extensive PBE carries the generated source
history, terminality proof, and exact finite `B*` dropout trace.
-/
theorem theorem8_belief_source_extensive_pbe_history_terminal_exact_drop_history
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    (hpbe :
      (terminalRecordBeliefSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        strategy terminal.initialState terminal.finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        strategy terminal.finalState ∧
        PaperTheorem8BStarRankedThresholdExactDropHistory
          terminal.localModel terminal.initialState terminal.finalState := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_history_terminal_exact_drop_history
      terminal hpbe

/--
Belief-explicit all-terminal VCG conclusion.  If the audited no-overshoot
terminal state has no active ranks, the non-vacuous belief checker has a unique
PBE with the VCG outcome, rankwise slot/payment equality, and bidder utility
equality.
-/
theorem theorem8_belief_source_extensive_all_terminal_vcg_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome ∧
          (∀ rank,
            (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
              (G.outcomeOf strategy).paymentPerClick rank =
                G.vcgOutcome.paymentPerClick rank) ∧
            ∀ bidder,
              (G.outcomeOf strategy).utility G.environment G.values bidder =
                G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordBeliefSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_all_terminal_vcg_conclusion_of_no_overshoot
      terminal hno_active

/--
The same source-extensive PBE check written in the paper's one-step
best-response and at-threshold tie-break obligations.
-/
theorem theorem8_source_extensive_pbe_iff_one_step_best_response_and_drop_at_threshold
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy ∧
        paper_theorem8_bstar_ranked_threshold_drop_at_threshold_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold
      terminal strategy

/--
The terminal-record source-shaped checker in the same one-step/tie-break form.
-/
theorem theorem8_terminal_record_source_pbe_iff_one_step_best_response_and_drop_at_threshold
    (terminal :
      PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordSourceGame terminal).PerfectBayesianEquilibrium strategy ↔
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy ∧
        paper_theorem8_bstar_ranked_threshold_drop_at_threshold_statement
          terminal.localModel.clickThroughRate terminal.localModel.value
          terminal.localModel.remaining strategy := by
  simpa [terminalRecordSourceGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_pbe_iff_one_step_best_response_and_drop_at_threshold
      terminal strategy

/--
Finite ex-post source boundary: in the finite exact-history source object,
sequential rationality is exactly the audited local-deviation predicate, for
every strategy and belief.
-/
theorem theorem8_ex_post_finite_source_sequential_rationality_iff_local_deviation
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedFiniteExactHistoryExPostLocalDeviationSourceCompletionCertificate
        Belief)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ)
    (belief : Belief) :
    cert.source.integrated.dynamic.base.game.isSequentiallyRational
        strategy belief ↔
      paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.remaining
        strategy := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_sequential_rationality_iff_local_deviation
      cert strategy belief

/--
Finite ex-post source boundary: once the named finite `B*` strategy satisfies
the audited one-step best-response condition, it is sequentially rational for
every belief in the finite source object.
-/
theorem theorem8_ex_post_finite_source_named_strategy_sequentially_rational_for_all_beliefs
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedFiniteExactHistoryExPostLocalDeviationSourceCompletionCertificate
        Belief)
    (hbest :
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.remaining
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.source.integrated.dynamic.base.strictModel.value
          cert.source.integrated.dynamic.base.strictModel.clickThroughRate
          cert.source.integrated.dynamic.base.strictModel.remaining)) :
    ∀ belief : Belief,
      cert.source.integrated.dynamic.base.game.isSequentiallyRational
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.source.integrated.dynamic.base.strictModel.value
          cert.source.integrated.dynamic.base.strictModel.clickThroughRate
          cert.source.integrated.dynamic.base.strictModel.remaining)
        belief := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_named_strategy_sequentially_rational_for_all_beliefs
      cert hbest

/--
Finite ex-post source boundary, belief-free citation form: if the belief space
is nonempty, one-step best response for the named finite `B*` strategy
discharges the local-deviation rationality predicate used by the terminal
source-completion endpoint.
-/
theorem theorem8_ex_post_finite_source_named_strategy_local_deviation_of_one_step_best_response
    {Belief : Type*}
    [hbelief : Nonempty Belief]
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedFiniteExactHistoryExPostLocalDeviationSourceCompletionCertificate
        Belief)
    (hbest :
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.remaining
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.source.integrated.dynamic.base.strictModel.value
          cert.source.integrated.dynamic.base.strictModel.clickThroughRate
          cert.source.integrated.dynamic.base.strictModel.remaining)) :
    paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
      cert.source.integrated.dynamic.base.strictModel.clickThroughRate
      cert.source.integrated.dynamic.base.strictModel.value
      cert.source.integrated.dynamic.base.strictModel.remaining
      (paper_theorem8_bstar_ranked_threshold_strategy
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.remaining) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_named_strategy_local_deviation_of_one_step_best_response_of_nonempty_beliefs
      cert hbest

/--
Finite ex-post source boundary with the named finite `B*` one-step
best-response proof discharged by the strict model rather than passed as a
paper-facing assumption.
-/
theorem theorem8_ex_post_finite_source_named_strategy_sequentially_rational_for_all_beliefs_of_strict_model
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedFiniteExactHistoryExPostLocalDeviationSourceCompletionCertificate
        Belief) :
    ∀ belief : Belief,
      cert.source.integrated.dynamic.base.game.isSequentiallyRational
        (paper_theorem8_bstar_ranked_threshold_strategy
          cert.source.integrated.dynamic.base.strictModel.value
          cert.source.integrated.dynamic.base.strictModel.clickThroughRate
          cert.source.integrated.dynamic.base.strictModel.remaining)
        belief := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_named_strategy_sequentially_rational_for_all_beliefs_of_strict_model
      cert

/--
Finite ex-post source boundary, belief-free citation form: the named finite
`B*` strategy satisfies the local-deviation rationality predicate from the
strict model alone.
-/
theorem theorem8_ex_post_finite_source_named_strategy_local_deviation_of_strict_model
    {Belief : Type*}
    [hbelief : Nonempty Belief]
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedFiniteExactHistoryExPostLocalDeviationSourceCompletionCertificate
        Belief) :
    paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
      cert.source.integrated.dynamic.base.strictModel.clickThroughRate
      cert.source.integrated.dynamic.base.strictModel.value
      cert.source.integrated.dynamic.base.strictModel.remaining
      (paper_theorem8_bstar_ranked_threshold_strategy
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.remaining) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_named_strategy_local_deviation_of_strict_model
      cert

/--
Core ex-post local-deviation source ledger with the named finite `B*`
strategy's ex-post sequential rationality discharged from the strict model.
-/
theorem theorem8_ex_post_local_deviation_core_source_obligations_of_strict_model
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationCoreSourceCompletionCertificate
        Belief) :
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.integrated.dynamic.base.strictModel.value
        cert.integrated.dynamic.base.strictModel.clickThroughRate
        cert.integrated.dynamic.base.strictModel.remaining
    cert.integrated.dynamic.base.game.isConsistentBelief
        namedStrategy cert.integrated.dynamic.base.belief ∧
      (∀ belief : Belief,
          cert.integrated.dynamic.base.game.isSequentiallyRational
            namedStrategy belief) ∧
        ∀ strategy belief,
          cert.integrated.dynamic.base.game.isSequentiallyRational
              strategy belief ↔
            paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
              cert.integrated.dynamic.base.strictModel.clickThroughRate
              cert.integrated.dynamic.base.strictModel.value
              cert.integrated.dynamic.base.strictModel.remaining
              strategy := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_core_source_completion_obligations_of_strict_model
      cert

/--
Finite ex-post source-completion obligation ledger with the named finite `B*`
strategy's ex-post sequential rationality discharged from the strict model.
-/
theorem theorem8_ex_post_finite_source_obligations_of_strict_model
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedFiniteExactHistoryExPostLocalDeviationSourceCompletionCertificate
        Belief) :
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.remaining
    cert.source.integrated.dynamic.base.game.isConsistentBelief
        namedStrategy cert.source.integrated.dynamic.base.belief ∧
      (∀ belief : Belief,
          cert.source.integrated.dynamic.base.game.isSequentiallyRational
            namedStrategy belief) ∧
      (∀ strategy belief,
        cert.source.integrated.dynamic.base.game.isSequentiallyRational
            strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
            cert.source.integrated.dynamic.base.strictModel.clickThroughRate
            cert.source.integrated.dynamic.base.strictModel.value
            cert.source.integrated.dynamic.base.strictModel.remaining
            strategy) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        cert.source.integrated.terminal.localModel
        cert.source.integrated.terminal.initialState
        cert.source.integrated.terminal.finalState ∧
        ∀ rank, rank ∈ cert.completedRanks →
          ¬ cert.source.integrated.terminal.finalState.IsActive rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_exact_history_ex_post_local_deviation_source_completion_obligations_of_strict_model
      cert

/--
Theorem 8 source-shaped finite-schedule endpoint.  From strict ordered paper
assumptions and a sorted no-duplicate finite dropout schedule, the
source-shaped dynamic game has a unique PBE with the full ordered
terminal/dynamic conclusion.  The source-shaped dynamic certificate supplies
belief consistency and the sequential-rationality/source predicate internally.
-/
theorem theorem8_source_sequential_schedule_full_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model initialState).base.strictModel)
        initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel)
            initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.remaining + 1)
              (rank + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_terminal_dynamic_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
          model initialState)
        initialState scheduledRanks hsorted hnodup hinitial_active hunscheduled
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          cert strategy := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_terminal_dynamic_exists_unique_pbe_with_full_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState scheduledRanks hsorted hnodup hinitial_active
      hunscheduled

/--
Trace-refined source-shaped finite-schedule endpoint.  This is the strongest
paper-facing source route from sorted no-duplicate schedule data: the
source-shaped dynamic game has a unique PBE, the PBE is the named finite `B*`
strategy, the full terminal/dynamic/ordered-outcome conclusion holds, and the
generated terminal history is exposed together with terminality and the exact
finite `B*` dropout trace.
-/
theorem theorem8_source_sequential_schedule_trace_full_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model initialState).base.strictModel)
        initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel)
            initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.remaining + 1)
              (rank + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
          model initialState)
        initialState scheduledRanks hsorted hnodup hinitial_active hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                  cert.terminal.localModel cert.terminal.initialState
                  cert.terminal.finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState scheduledRanks hsorted hnodup hinitial_active
      hunscheduled

/--
Trace-refined source-shaped finite-schedule endpoint with completed-rank
terminal-record formulas.  This extends the trace-full schedule theorem by
also displaying the slot, finite `B*` payment, VCG-tail accounting, and payment
bounds for every completed rank included in the schedule.
-/
theorem theorem8_source_sequential_schedule_trace_full_completed_rank_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model initialState).base.strictModel)
        initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel)
            initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model initialState).base.strictModel.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
          model initialState)
        initialState scheduledRanks hsorted hnodup hinitial_active
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hunscheduled rank hnot_mem)
      hsubset

/--
Cold-start threshold-sorted source-shaped trace endpoint.  This is the
least-noisy finite-schedule source route for paper checks: threshold-sorted
schedule, no duplicates, and the unscheduled-threshold condition imply unique
PBE, named finite `B*` strategy, full terminal/dynamic/ordered-outcome
conclusion, generated history, terminality, and exact finite `B*` dropout trace.
-/
theorem theorem8_source_sequential_cold_start_threshold_sorted_trace_full_conclusion
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
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let scheduledRanks := scheduledPrefix ++ [lastRank]
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
          model paper_theorem8_bstar_ranked_threshold_cold_start_state)
        paper_theorem8_bstar_ranked_threshold_cold_start_state scheduledRanks
        (by
          simpa [scheduledRanks,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_source_sequential_constructed_outcome_certificate_of_local_optimality,
            paper_theorem8_bstar_ranked_threshold_strict_local_deviation_constructed_outcome_certificate_of_local_optimality] using
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_of_threshold_sorted
              model (scheduledPrefix ++ [lastRank]) hthreshold_sorted)
        hnodup (fun rank => by rfl)
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid, scheduledRanks,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_source_sequential_constructed_outcome_certificate_of_local_optimality,
            paper_theorem8_bstar_ranked_threshold_strict_local_deviation_constructed_outcome_certificate_of_local_optimality] using
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              paper_theorem8_bstar_ranked_threshold_cold_start_state
              scheduledPrefix lastRank
              (by
                intro rank hrank
                simpa [theorem8BStarThresholdBid] using
                  hunscheduled_last rank hrank)
              rank hnot_mem)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                  cert.terminal.localModel cert.terminal.initialState
                  cert.terminal.finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_conclusion_of_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model scheduledPrefix lastRank hthreshold_sorted hnodup
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hunscheduled_last rank hrank)

/--
Cold-start threshold-sorted source-shaped trace endpoint with completed-rank
terminal-record formulas.  This is the compact cold-start paper-checking form
when the reviewer wants both the full source/dynamic trace and the displayed
finite completed-rank payment formulas.
-/
theorem theorem8_source_sequential_cold_start_threshold_sorted_trace_full_completed_rank_conclusion
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
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledPrefix ++ [lastRank]) :
    let scheduledRanks := scheduledPrefix ++ [lastRank]
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
          model paper_theorem8_bstar_ranked_threshold_cold_start_state)
        paper_theorem8_bstar_ranked_threshold_cold_start_state scheduledRanks
        (by
          simpa [scheduledRanks,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_source_sequential_constructed_outcome_certificate_of_local_optimality,
            paper_theorem8_bstar_ranked_threshold_strict_local_deviation_constructed_outcome_certificate_of_local_optimality] using
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_of_threshold_sorted
              model (scheduledPrefix ++ [lastRank]) hthreshold_sorted)
        hnodup (fun rank => by rfl)
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid, scheduledRanks,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate,
            paper_theorem8_bstar_ranked_threshold_strict_source_sequential_constructed_outcome_certificate_of_local_optimality,
            paper_theorem8_bstar_ranked_threshold_strict_local_deviation_constructed_outcome_certificate_of_local_optimality] using
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              paper_theorem8_bstar_ranked_threshold_cold_start_state
              scheduledPrefix lastRank
              (by
                intro rank hrank
                simpa [theorem8BStarThresholdBid] using
                  hunscheduled_last rank hrank)
              rank hnot_mem)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model completedRanks scheduledPrefix lastRank hthreshold_sorted hnodup
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hunscheduled_last rank hrank)
      hsubset

/--
Clock-disciplined source-shaped trace endpoint.  This is the schedule-free
version of the trace-full source route: any clock-disciplined terminal history
for the source-shaped dynamic certificate gives unique PBE, named finite `B*`
strategy, full terminal/dynamic/ordered-outcome conclusion, generated history,
terminality, and exact finite `B*` dropout trace.
-/
theorem theorem8_clock_disciplined_terminal_history_source_trace_full_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel)
        state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel.value
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel.clickThroughRate
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    let dynamic :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model state
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist
        (by
          intro rank hactive
          simpa [theorem8BStarThresholdBid] using
            hstate_no_overshoot rank hactive)
        terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                  cert.terminal.localModel cert.terminal.initialState
                  cert.terminal.finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_conclusion_of_clock_disciplined_strategy_history
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model state)
      hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active

/--
Clock-disciplined source-shaped trace endpoint with completed-rank
terminal-record formulas.  This is the schedule-free source route when the
source history is already available: Lean derives unique PBE, the named
finite `B*` strategy, the full terminal/dynamic/ordered-outcome conclusion,
generated history, terminality, exact records, and displayed formulas for
every completed rank.
-/
theorem theorem8_clock_disciplined_terminal_history_source_trace_full_completed_rank_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel)
        state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel.value
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel.clickThroughRate
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model state).base.strictModel.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model state).base.strictModel.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice) :
    let dynamic :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model state
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_clock_disciplined_strategy_history
        dynamic hhist
        (by
          intro rank hactive
          simpa [theorem8BStarThresholdBid] using
            hstate_no_overshoot rank hactive)
        terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_clock_disciplined_strategy_history
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model state)
      hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Cold-start clock-disciplined source-shaped trace endpoint.  The source history
starts at the paper's cold-start state, so Lean derives the initial
no-overshoot timing premise and initial activity internally.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_trace_full_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.value
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.clickThroughRate
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.remaining)
        finalState) :
    let dynamic :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
        dynamic hhist terminal
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_conclusion_of_cold_start_clock_disciplined_strategy_history
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model paper_theorem8_bstar_ranked_threshold_cold_start_state)
      hhist terminal

/--
Cold-start clock-disciplined source-shaped trace endpoint with completed-rank
terminal-record formulas.  The source history starts at the paper's cold-start
state, so Lean derives the initial no-overshoot timing premise and initial
activity internally.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_trace_full_completed_rank_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel)
        paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.value
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.clickThroughRate
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
                model paper_theorem8_bstar_ranked_threshold_cold_start_state).base.strictModel.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice) :
    let dynamic :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_of_cold_start_clock_disciplined_strategy_history
        dynamic hhist terminal
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_cold_start_clock_disciplined_strategy_history
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
        model paper_theorem8_bstar_ranked_threshold_cold_start_state)
      hhist terminal completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Generic no-overshoot terminal/dynamic trace endpoint with completed-rank
terminal-record formulas.  This is the compact citation form when a source
proof has already produced a no-overshoot terminal/dynamic certificate and a
finite set of ranks whose thresholds are reached by the terminal clock.
-/
theorem theorem8_no_overshoot_terminal_dynamic_trace_full_completed_threshold_conclusion
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              cert.terminal.localModel.value cert.terminal.localModel.clickThroughRate
              (cert.terminal.localModel.remaining + 1) (rank + 1) ≤
            cert.terminal.finalState.clockPrice) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion
      cert completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Generic no-overshoot terminal/dynamic trace endpoint with completed-rank
terminal-record formulas from direct final inactivity. Use this when the source
proof identifies the completed rank set by terminal inactivity rather than by
terminal-clock threshold inequalities.
-/
theorem theorem8_no_overshoot_terminal_dynamic_trace_full_completed_rank_conclusion
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedNoOvershootTerminalDynamicCertificate
        Belief)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks →
        ¬ cert.terminal.finalState.IsActive rank) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_inactive_completed
      cert completedRanks inactive_on_completed

/--
Source-sequential no-overshoot terminal-history full conclusion where the
strict ordered assumptions are stated directly on the terminal certificate's
local model. This avoids a separate model-equality proof when the audited
terminal history is the source of truth for the finite `B*` model.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_full_conclusion_of_terminal_model_assumptions
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (current_lt : ∀ rank,
      terminal.localModel.clickThroughRate (rank + 1) <
        terminal.localModel.clickThroughRate rank)
    (value_nonneg : ∀ rank, 0 ≤ terminal.localModel.value rank)
    (value_mono : ∀ rank,
      terminal.localModel.value (rank + 1) ≤ terminal.localModel.value rank)
    (continuation_tail_payment_lt : ∀ rank,
      paper_theorem7_ranked_vcg_tail_payment
          terminal.localModel.value terminal.localModel.clickThroughRate
          (rank + 1) terminal.localModel.remaining <
        terminal.localModel.clickThroughRate (rank + 1) *
          terminal.localModel.value (rank + 1)) :
    let model :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_optimality_certificate_of_local_model
        terminal.localModel current_lt value_nonneg value_mono
        continuation_tail_payment_lt
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict_ordered_local_model_eq
          terminal.localModel current_lt value_nonneg value_mono
          continuation_tail_payment_lt)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          ordinary strategy := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_exists_unique_pbe_with_full_conclusion_of_terminal_model
      terminal current_lt value_nonneg value_mono continuation_tail_payment_lt

/--
Source-sequential no-overshoot terminal-history trace endpoint.  This is the
source-shaped terminal-history citation form when the review should display
unique PBE, named strategy, generated history, terminality, exact dropout
records, and completed-rank terminal-record formulas together.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model terminal.initialState).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model hmodel
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le
      terminal model hmodel completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Source-sequential no-overshoot terminal-history trace endpoint with completed
ranks supplied directly as terminal-inactive ranks. This is the trace-rich
source-facing citation form when the proof already identifies completed ranks
from the terminal history.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model terminal.initialState).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model hmodel
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_inactive_completed
      terminal model hmodel completedRanks inactive_on_completed

/--
Terminal-local source-sequential trace endpoint.  This is the same rich
completed-rank review form as above, but it states the strict ordered
assumptions directly on the annotated terminal certificate's local model and
therefore avoids a separate model-equality proof.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_threshold_conclusion_of_terminal_model_assumptions
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (current_lt : ∀ rank,
      terminal.localModel.clickThroughRate (rank + 1) <
        terminal.localModel.clickThroughRate rank)
    (value_nonneg : ∀ rank, 0 ≤ terminal.localModel.value rank)
    (value_mono : ∀ rank,
      terminal.localModel.value (rank + 1) ≤ terminal.localModel.value rank)
    (continuation_tail_payment_lt : ∀ rank,
      paper_theorem7_ranked_vcg_tail_payment
          terminal.localModel.value terminal.localModel.clickThroughRate
          (rank + 1) terminal.localModel.remaining <
        terminal.localModel.clickThroughRate (rank + 1) *
          terminal.localModel.value (rank + 1))
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice) :
    let model :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_optimality_certificate_of_local_model
        terminal.localModel current_lt value_nonneg value_mono
        continuation_tail_payment_lt
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict_ordered_local_model_eq
          terminal.localModel current_lt value_nonneg value_mono
          continuation_tail_payment_lt)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_terminal_model
      terminal current_lt value_nonneg value_mono continuation_tail_payment_lt
      completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Terminal-local source-sequential trace endpoint with direct completed-rank
inactivity instead of a terminal-clock threshold premise.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_trace_full_completed_rank_conclusion_of_terminal_model_assumptions
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (current_lt : ∀ rank,
      terminal.localModel.clickThroughRate (rank + 1) <
        terminal.localModel.clickThroughRate rank)
    (value_nonneg : ∀ rank, 0 ≤ terminal.localModel.value rank)
    (value_mono : ∀ rank,
      terminal.localModel.value (rank + 1) ≤ terminal.localModel.value rank)
    (continuation_tail_payment_lt : ∀ rank,
      paper_theorem7_ranked_vcg_tail_payment
          terminal.localModel.value terminal.localModel.clickThroughRate
          (rank + 1) terminal.localModel.remaining <
        terminal.localModel.clickThroughRate (rank + 1) *
          terminal.localModel.value (rank + 1))
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank) :
    let model :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_optimality_certificate_of_local_model
        terminal.localModel current_lt value_nonneg value_mono
        continuation_tail_payment_lt
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model
        (paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict_ordered_local_model_eq
          terminal.localModel current_lt value_nonneg value_mono
          continuation_tail_payment_lt)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_terminal_model_inactive_completed
      terminal current_lt value_nonneg value_mono continuation_tail_payment_lt
      completedRanks inactive_on_completed

/--
Theorem 8 ex-post local-deviation finite-schedule source-completion endpoint.
From the belief-independent local-deviation source certificate and a sorted
no-duplicate finite dropout schedule, Lean derives unique PBE plus the
displayed terminal-record formulas for every scheduled rank.
-/
theorem theorem8_ex_post_local_deviation_finite_schedule_all_completed_source_completion
    {Belief : Type*}
    (source :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationCoreSourceCompletionCertificate
        Belief)
    (scheduledRanks : List ℕ)
    (hfinal :
      source.integrated.terminal.finalState =
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          source.integrated.terminal.localModel
          source.integrated.terminal.initialState
          scheduledRanks)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        source.integrated.terminal.localModel
        source.integrated.terminal.initialState.clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup) :
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      source.integrated.dynamic.base.game.PerfectBayesianEquilibrium
          strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          source.integrated strategy ∧
          ∀ rank,
            rank ∈ scheduledRanks.toFinset →
              (paper_theorem8_terminal_dropout_record_outcome
                source.integrated.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  source.integrated.terminal.finalState).paymentPerClick
                    rank =
                  theorem8BStarThresholdBid
                    source.integrated.terminal.localModel.value
                    source.integrated.terminal.localModel.clickThroughRate
                    (source.integrated.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  source.integrated.terminal.localModel.clickThroughRate rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        source.integrated.terminal.finalState).paymentPerClick
                        rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      source.integrated.terminal.localModel.value
                      source.integrated.terminal.localModel.clickThroughRate
                      rank
                      (source.integrated.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        source.integrated.terminal.finalState).paymentPerClick
                        rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        source.integrated.terminal.finalState).paymentPerClick
                        rank ≤
                        source.integrated.terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_ex_post_local_deviation_source_completion_of_clock_sorted_nodup
      source scheduledRanks hfinal hsorted hnodup

/--
Cold-start threshold-sorted ex-post local-deviation source-completion endpoint.
From strict ordered paper assumptions and a threshold-sorted finite schedule,
Lean constructs the finite source certificate and returns unique PBE plus the
terminal-record formulas on every scheduled rank.
-/
theorem theorem8_ex_post_local_deviation_cold_start_threshold_sorted_all_completed_source_completion
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
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_ex_post_local_deviation_source_completion_certificate_of_local_deviation_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
        model scheduledPrefix lastRank hthreshold_sorted hnodup
        (by
          intro rank hrank
          simpa [theorem8BStarThresholdBid] using
            hunscheduled_last rank hrank)
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.source.integrated.dynamic.base.game.PerfectBayesianEquilibrium
          strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          cert.source.integrated strategy ∧
          ∀ rank,
            rank ∈ cert.completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.source.integrated.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.source.integrated.terminal.finalState).paymentPerClick
                    rank =
                  theorem8BStarThresholdBid
                    cert.source.integrated.terminal.localModel.value
                    cert.source.integrated.terminal.localModel.clickThroughRate
                    (cert.source.integrated.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.source.integrated.terminal.localModel.clickThroughRate
                      rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.source.integrated.terminal.localModel.value
                      cert.source.integrated.terminal.localModel.clickThroughRate
                      rank
                      (cert.source.integrated.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank ≤
                        cert.source.integrated.terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_schedule_all_scheduled_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_local_deviation_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model scheduledPrefix lastRank hthreshold_sorted hnodup
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hunscheduled_last rank hrank)

/--
All-rank ex-post local-deviation exact-history source boundary.  This is the
compact obligation ledger for the fully exact source route: the source side
supplies belief consistency, belief-independent sequential rationality of the
named strategy from one-step best response, and the local-deviation iff; the
history side supplies exact finite `B*` records and all-rank terminality.
-/
theorem theorem8_ex_post_local_deviation_exact_history_source_obligations
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationExactHistorySourceCompletionCertificate
        Belief) :
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.remaining
    cert.source.integrated.dynamic.base.game.isConsistentBelief
        namedStrategy cert.source.integrated.dynamic.base.belief ∧
      (∀ belief : Belief,
        paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
            cert.source.integrated.dynamic.base.strictModel.clickThroughRate
            cert.source.integrated.dynamic.base.strictModel.value
            cert.source.integrated.dynamic.base.strictModel.remaining
            namedStrategy →
          cert.source.integrated.dynamic.base.game.isSequentiallyRational
            namedStrategy belief) ∧
      (∀ strategy belief,
        cert.source.integrated.dynamic.base.game.isSequentiallyRational
            strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
            cert.source.integrated.dynamic.base.strictModel.clickThroughRate
            cert.source.integrated.dynamic.base.strictModel.value
            cert.source.integrated.dynamic.base.strictModel.remaining
            strategy) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        cert.source.integrated.terminal.localModel
        cert.source.integrated.terminal.initialState
        cert.source.integrated.terminal.finalState ∧
        ∀ rank, ¬ cert.source.integrated.terminal.finalState.IsActive rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_exact_history_source_completion_obligations
      cert

/--
All-rank ex-post local-deviation exact-history source ledger with the named
finite `B*` strategy's ex-post sequential rationality discharged from the
strict model.
-/
theorem theorem8_ex_post_local_deviation_exact_history_source_obligations_of_strict_model
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationExactHistorySourceCompletionCertificate
        Belief) :
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.source.integrated.dynamic.base.strictModel.value
        cert.source.integrated.dynamic.base.strictModel.clickThroughRate
        cert.source.integrated.dynamic.base.strictModel.remaining
    cert.source.integrated.dynamic.base.game.isConsistentBelief
        namedStrategy cert.source.integrated.dynamic.base.belief ∧
      (∀ belief : Belief,
          cert.source.integrated.dynamic.base.game.isSequentiallyRational
            namedStrategy belief) ∧
      (∀ strategy belief,
        cert.source.integrated.dynamic.base.game.isSequentiallyRational
            strategy belief ↔
          paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
            cert.source.integrated.dynamic.base.strictModel.clickThroughRate
            cert.source.integrated.dynamic.base.strictModel.value
            cert.source.integrated.dynamic.base.strictModel.remaining
            strategy) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        cert.source.integrated.terminal.localModel
        cert.source.integrated.terminal.initialState
        cert.source.integrated.terminal.finalState ∧
        ∀ rank, ¬ cert.source.integrated.terminal.finalState.IsActive rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_exact_history_source_completion_obligations_of_strict_model
      cert

/--
All-rank ex-post local-deviation exact-history source endpoint.  Once the
obligation ledger above is packaged as a certificate, Lean derives unique PBE,
the terminal/dynamic Theorem 8 conclusion, and equality between the terminal
dropout-record outcome and the constructed ranked finite `B*` outcome.
-/
theorem theorem8_ex_post_local_deviation_exact_history_source_terminal_record_outcome_eq_bstar
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationExactHistorySourceCompletionCertificate
        Belief) :
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.source.integrated.dynamic.base.game.PerfectBayesianEquilibrium
          strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          cert.source.integrated strategy ∧
          paper_theorem8_terminal_dropout_record_outcome
              cert.source.integrated.terminal.finalState =
            paper_theorem8_bstar_ranked_threshold_outcome
              cert.source.integrated.terminal.localModel.value
              cert.source.integrated.terminal.localModel.clickThroughRate
              (cert.source.integrated.terminal.localModel.remaining + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_exact_history_source_completion_exists_unique_pbe_with_terminal_record_outcome_eq_bstar
      cert

/--
All-rank ex-post local-deviation exact-history source endpoint with the full
terminal/dynamic/ordered-outcome conclusion.  This is the strongest compact
paper-facing route once exact source history and all-rank terminality are
available.
-/
theorem theorem8_ex_post_local_deviation_exact_history_source_full_conclusion_terminal_record_outcome_eq_bstar
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationExactHistorySourceCompletionCertificate
        Belief) :
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.source.integrated.dynamic.base.game.PerfectBayesianEquilibrium
          strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
          cert.source.integrated strategy ∧
          paper_theorem8_terminal_dropout_record_outcome
              cert.source.integrated.terminal.finalState =
            paper_theorem8_bstar_ranked_threshold_outcome
              cert.source.integrated.terminal.localModel.value
              cert.source.integrated.terminal.localModel.clickThroughRate
              (cert.source.integrated.terminal.localModel.remaining + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_exact_history_source_completion_exists_unique_pbe_with_full_conclusion_and_terminal_record_outcome_eq_bstar
      cert

/--
All-rank ex-post local-deviation exact-history source utility endpoint.  The
terminal dropout-record outcome gives each rank the same utility as the
constructed successor-tail ranked finite `B*` outcome.
-/
theorem theorem8_ex_post_local_deviation_exact_history_source_terminal_record_utility_eq_bstar
    {Belief : Type*}
    (cert :
      PaperTheorem8BStarRankedThresholdStrictOrderedExPostLocalDeviationExactHistorySourceCompletionCertificate
        Belief)
    (rank : ℕ) :
    (paper_theorem8_terminal_dropout_record_outcome
        cert.source.integrated.terminal.finalState).utility
        ({ clickThroughRate :=
            cert.source.integrated.terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        cert.source.integrated.terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        cert.source.integrated.terminal.localModel.value
        cert.source.integrated.terminal.localModel.clickThroughRate
        (cert.source.integrated.terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate :=
            cert.source.integrated.terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        cert.source.integrated.terminal.localModel.value rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_ex_post_local_deviation_exact_history_source_completion_terminal_record_utility_eq_bstar
      cert rank

/--
Theorem 8 terminal-record source-shaped finite-schedule endpoint.  From a
sorted no-duplicate finite `B*` dropout schedule, Lean builds the no-overshoot
terminal history and exact terminal records, then derives unique PBE and the
displayed completed-rank formula.
-/
theorem theorem8_terminal_record_source_schedule_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceGame ordinary
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
Cold-start paper-checking form of the terminal-record source-shaped endpoint.
The input schedule is threshold-sorted rather than recursively clock-sorted,
and Lean generates the no-overshoot terminal history and exact records.
-/
theorem theorem8_terminal_record_source_cold_start_threshold_sorted_conclusion
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
            theorem8BStarThresholdBid
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
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceGame ordinary
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_strict_ordered_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model completedRanks scheduledPrefix lastRank hthreshold_sorted hnodup
      hunscheduled_last hsubset

/--
Theorem 8 source-extensive no-overshoot terminal-history endpoint.  This is the
generic source-history form behind the finite schedule wrappers: the terminal
certificate carries a concrete no-overshoot generalized-English history, and
the resulting PBE predicate includes source sequential rationality, the
generated history, terminality, and the displayed completed-rank formula.
-/
theorem theorem8_no_overshoot_terminal_record_source_extensive_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot
      terminal completedRanks inactive_on_completed hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Theorem 8 source-extensive no-overshoot terminal-history endpoint with the
paper-facing terminal-clock premise.  If each completed rank's finite `B*`
threshold has been reached by the terminal clock, Lean derives completed-rank
inactivity, unique PBE, source history/terminality inside PBE, and the displayed
completed-rank formula.
-/
theorem theorem8_no_overshoot_terminal_record_source_extensive_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      terminal completedRanks hcompleted_threshold_le hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Trace-refined no-overshoot source-extensive endpoint with the direct
completed-rank inactivity premise.  This is the source-proof shape to use when
the audited history has already established that the displayed finite rank set
has dropped out, without routing through a terminal-clock inequality.
-/
theorem theorem8_no_overshoot_terminal_record_source_extensive_trace_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        terminal.localModel.value terminal.localModel.clickThroughRate
        terminal.localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  dsimp [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid]
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game
      terminal
  let namedStrategy :=
    paper_theorem8_bstar_ranked_threshold_strategy
      terminal.localModel.value terminal.localModel.clickThroughRate
      terminal.localModel.remaining
  refine ⟨namedStrategy, ?_, ?_⟩
  · have hpbe : G.PerfectBayesianEquilibrium namedStrategy := by
      exact
        (paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_named_strategy
          terminal namedStrategy).mpr rfl
    have htrace :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_history_terminal_exact_drop_history
        terminal hpbe
    refine ⟨hpbe, rfl, htrace.1, htrace.2.1, htrace.2.2, ?_⟩
    intro rank hrank
    exact
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_completed_rank_paper_conclusion_of_no_overshoot
        terminal completedRanks inactive_on_completed hvalue_nonneg
        hvalue_mono hclick_mono hclick_pos hpbe rank hrank
  · intro strategy hstrategy
    exact hstrategy.2.1

/--
Ordinary strategy-consistent histories are not enough to recover exact finite
`B*` terminal records.  This witness has a terminal named-strategy history in
which the only active rank drops after its finite `B*` threshold, so its
terminal dropout record is not the exact paper threshold.
-/
theorem theorem8_ordinary_strategy_history_allows_overshoot_record
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (rank : ℕ) :
    let state :=
      paper_theorem8_bstar_ranked_threshold_single_active_overshoot_state
        model rank
    let finalState :=
      PaperTheorem8GeneralizedEnglishAuctionState.recordDropout state rank
    let threshold :=
      theorem8BStarThresholdBid
        model.value model.clickThroughRate (model.remaining + 1) (rank + 1)
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState ∧
        finalState.lastDropout rank = some (threshold + 1) ∧
          finalState.lastDropout rank ≠ some threshold := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_record
      model rank

/--
Same overshoot witness, stated as a non-exact-history guardrail.  A terminal
named-strategy history whose dropout record overshoots the finite `B*`
threshold cannot be used as an exact finite-`B*` dropout history.
-/
theorem theorem8_ordinary_strategy_history_allows_overshoot_not_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (rank : ℕ) :
    let state :=
      paper_theorem8_bstar_ranked_threshold_single_active_overshoot_state
        model rank
    let finalState :=
      PaperTheorem8GeneralizedEnglishAuctionState.recordDropout state rank
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState ∧
        ¬ PaperTheorem8BStarRankedThresholdExactDropHistory
          model state finalState := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_not_exact_drop_history
      model rank

/--
Source-extensive rationality alone does not recover exact finite `B*` dropout
records. The same overshoot witness satisfies the source-extensive rationality
boundary for the named strategy, but is not an exact-drop history.
-/
theorem theorem8_source_extensive_rationality_allows_overshoot_not_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (rank : ℕ) :
    let state :=
      paper_theorem8_bstar_ranked_threshold_single_active_overshoot_state
        model rank
    let finalState :=
      PaperTheorem8GeneralizedEnglishAuctionState.recordDropout state rank
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState namedStrategy ∧
      ¬ PaperTheorem8BStarRankedThresholdExactDropHistory
        model state finalState := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_allows_overshoot_not_exact_drop_history
      model rank

/--
Source-history bridge for arbitrary ordinary histories.  A history generated
by the named finite `B*` strategy has exact finite `B*` dropout records as soon
as each actual dropout step is known not to overshoot that rank's threshold.
-/
theorem theorem8_strategy_history_to_exact_drop_history_of_no_overshoot_drop_steps
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      ∀ state rank,
        state.IsActive rank →
          paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining state rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_to_exact_drop_history_of_no_overshoot_drop_steps
      model hhist hno_overshoot

/--
At a realized named-strategy dropout step, the exact-record obligation is local:
strategy consistency gives that the clock reached the finite `B*` threshold,
and the no-overshoot premise gives the reverse inequality. Therefore the new
dropout record is exactly the finite `B*` threshold price.
-/
theorem theorem8_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hstep :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) state next)
    (hactive : state.IsActive rank) (hinactive : ¬ next.IsActive rank)
    (hno_overshoot :
      state.clockPrice ≤
        theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) :
    next.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  have hrecord_and_threshold :=
    paper_theorem8_bstar_ranked_threshold_strategy_step_new_dropout_record_eq_and_threshold_le
      model hstep hactive hinactive
  have hclock :
      state.clockPrice =
        paper_theorem8_bstar_threshold_bid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1) := by
    exact
      le_antisymm
        (by simpa [theorem8BStarThresholdBid] using hno_overshoot)
        hrecord_and_threshold.2
  simpa [theorem8BStarThresholdBid, hclock] using hrecord_and_threshold.1

/--
Clock-disciplined source steps are ordinary strategy-consistent steps for the
named finite `B*` strategy after forgetting the clock-discipline annotation.
-/
theorem theorem8_clock_disciplined_strategy_step_to_strategy_step
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state next) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
      (paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining)
      state next := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_to_strategy_step
      model hstep

/--
One-step clock discipline preserves the active-rank no-overshoot invariant.
This is the source-step form of the timing invariant used by the exact-record
bridge.
-/
theorem theorem8_clock_disciplined_strategy_step_preserves_state_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state next)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∀ rank,
      next.IsActive rank →
        next.clockPrice ≤
          theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_preserves_state_no_overshoot
      model hstep
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)

/--
At any realized new dropout of a clock-disciplined source step, the pre-dropout
clock has not overshot the dropping rank's finite `B*` threshold, assuming the
pre-step state satisfies the active-rank no-overshoot invariant.
-/
theorem theorem8_clock_disciplined_strategy_step_realized_new_dropout_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state next)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hactive : state.IsActive rank)
    (hinactive : ¬ next.IsActive rank) :
    state.clockPrice ≤
      theorem8BStarThresholdBid
        model.value model.clickThroughRate (model.remaining + 1)
        (rank + 1) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_realized_new_dropout_no_overshoot
      model hstep
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      hactive hinactive

/--
At any realized new dropout of a clock-disciplined source step, the new
dropout record is exactly the rank's finite `B*` threshold. This packages the
one-step exact-record bridge needed by source-transition proofs.
-/
theorem theorem8_clock_disciplined_strategy_step_new_dropout_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state next)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hactive : state.IsActive rank)
    (hinactive : ¬ next.IsActive rank) :
    next.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_new_dropout_record_eq_threshold
      model hstep
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      hactive hinactive

/--
A clock-disciplined source step is the corresponding one-step
clock-disciplined history.
-/
theorem theorem8_clock_disciplined_strategy_step_to_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state next) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state next := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_to_history
      model hstep

/--
A single clock-disciplined source step is a one-step finite trace.
-/
theorem theorem8_clock_disciplined_strategy_step_to_trace
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model state next) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state next := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_step_to_trace
      model hstep

/--
A finite trace of clock-disciplined source steps induces the existing
clock-disciplined history object consumed by the terminal-record endpoints.
-/
theorem theorem8_clock_disciplined_strategy_trace_to_clock_disciplined_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_clock_disciplined_strategy_history
      model htrace

/--
Clock-disciplined source histories compose. This is useful when source
semantics prove separate clock-disciplined segments.
-/
theorem theorem8_clock_disciplined_strategy_history_trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hfirst :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state midState)
    (hsecond :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model midState finalState) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state finalState := by
  exact
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory.trans
      model hfirst hsecond

/--
Finite clock-disciplined source traces compose. This lets the source proof
assemble a finite trace from independently checked transition blocks.
-/
theorem theorem8_clock_disciplined_strategy_trace_trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hfirst :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state midState)
    (hsecond :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model midState finalState) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  exact
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace.trans
      model hfirst hsecond

/--
Append one checked clock-disciplined source step to an existing finite trace.
-/
theorem theorem8_clock_disciplined_strategy_trace_append_step
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state mid finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state mid)
    (hstep :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
        model mid finalState) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_append_step
      model htrace hstep

/--
An ordinary named-strategy source step becomes clock-disciplined when its
advance case is known not to pass any active rank's finite `B*` threshold.
-/
theorem theorem8_strategy_step_to_clock_disciplined_strategy_step_of_advance_safe
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
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyStep
      model state next := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strategy_step_to_clock_disciplined_strategy_step_of_advance_safe
      model hstep
      (by
        intro newPrice hnext rank hactive
        simpa [theorem8BStarThresholdBid] using
          hadvance_safe newPrice hnext rank hactive)

/--
An ordinary named-strategy source history becomes an explicit
clock-disciplined trace when every realized clock-advance step satisfies the
active-rank advance-safety bound.
-/
theorem theorem8_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
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
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_to_clock_disciplined_strategy_trace_of_advance_safe
      model hhist
      (by
        intro stepState stepNext newPrice hstep hnext rank hactive
        simpa [theorem8BStarThresholdBid] using
          hadvance_safe hstep hnext rank hactive)

/--
Source-extensive rationality plus an explicit advance-safety invariant
generates the finite clock-disciplined trace consumed by exact-record and PBE
endpoints.
-/
theorem theorem8_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
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
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_to_clock_disciplined_strategy_trace_of_advance_safe
      model hsource_extensive
      (by
        intro stepState stepNext newPrice hstep hnext rank hactive
        simpa [theorem8BStarThresholdBid] using
          hadvance_safe hstep hnext rank hactive)

/--
Source-extensive rationality, advance safety, and the initial active-rank
no-overshoot condition discharge the exact finite `B*` dropout-history
obligation.
-/
theorem theorem8_source_extensive_rationality_advance_safe_exact_drop_obligations
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
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate
                  (model.remaining + 1) (rank + 1))
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_advance_safe_exact_drop_obligations
      model hsource_extensive
      (by
        intro stepState stepNext newPrice hstep hnext rank hactive
        simpa [theorem8BStarThresholdBid] using
          hadvance_safe hstep hnext rank hactive)
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)

/--
Finite traces of clock-disciplined source steps preserve the active-rank
no-overshoot invariant from the initial state to the terminal state.
-/
theorem theorem8_clock_disciplined_strategy_trace_preserves_state_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∀ rank,
      finalState.IsActive rank →
        finalState.clockPrice ≤
          theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_preserves_state_no_overshoot
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)

/--
Finite traces of clock-disciplined source steps forget to ordinary
named-strategy histories.
-/
theorem theorem8_clock_disciplined_strategy_trace_to_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
      (paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining)
      state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_strategy_history
      model htrace

/--
Finite traces of clock-disciplined source steps induce no-overshoot source
histories under the initial active-rank no-overshoot premise.
-/
theorem theorem8_clock_disciplined_strategy_trace_to_no_overshoot_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_no_overshoot_strategy_history
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)

/--
Finite traces of clock-disciplined source steps give exact finite `B*` dropout
histories under the initial active-rank no-overshoot premise.
-/
theorem theorem8_clock_disciplined_strategy_trace_to_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_to_exact_drop_history
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)

/--
Clock-disciplined source histories discharge the two source obligations used
downstream: source-extensive rationality and exact finite `B*` dropout records.
This is the history-level counterpart of the finite trace wrapper below.
-/
theorem theorem8_clock_disciplined_strategy_history_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_source_extensive_exact_drop_obligations
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal

/--
Finite traces of clock-disciplined source steps discharge the two source
obligations used downstream: source-extensive rationality and exact finite
`B*` dropout records.
-/
theorem theorem8_clock_disciplined_strategy_trace_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_source_extensive_exact_drop_obligations
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal

/--
History-level source-invariant bridge: an ordinary named-strategy history
becomes a no-overshoot source history when every realized new-dropout step is
known not to overshoot that rank's finite `B*` threshold. This is the intended
interface between the real source transition proof and the existing
no-overshoot terminal-record endpoints.
-/
theorem theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      ∀ {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {rank : ℕ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining) state next →
        state.IsActive rank →
        ¬ next.IsActive rank →
        state.clockPrice ≤
          theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1)) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot
      model hhist
      (by
        intro state next rank hstep hactive hinactive
        simpa [theorem8BStarThresholdBid] using
          hno_overshoot hstep hactive hinactive)

/--
Named-statement form of the source-invariant bridge. A proof of
`theorem8RealizedNewDropoutNoOvershootStatement model` upgrades any ordinary
generated named-strategy history to the no-overshoot history object used by
the terminal-record endpoints.
-/
theorem theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot_statement
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      theorem8RealizedNewDropoutNoOvershootStatement model) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  simpa [theorem8RealizedNewDropoutNoOvershootStatement] using
    paper_theorem8_bstar_ranked_threshold_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot_statement
      model hhist hno_overshoot

/--
No-overshoot source histories forget to ordinary named-strategy histories. This
is the generated-history component of the tightest concrete timing certificate:
the no-overshoot evidence is stored only at realized dropout steps.
-/
theorem theorem8_no_overshoot_strategy_history_to_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
      (paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining)
      state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_no_overshoot_strategy_history_to_strategy_history
      model hhist

/--
No-overshoot source histories give exact finite `B*` dropout histories. This is
the direct route from realized no-overshoot timing to exact terminal records.
-/
theorem theorem8_no_overshoot_strategy_history_to_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_no_overshoot_strategy_history_to_exact_drop_history
      model hhist

/--
No-overshoot source histories compose. This lets a concrete source proof build
the timing-certified path from separately verified source-history segments.
-/
theorem theorem8_no_overshoot_strategy_history_trans
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state midState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hfirst :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state midState)
    (hsecond :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model midState finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  exact
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory.trans
      model hfirst hsecond

/--
Build the no-overshoot terminal-history certificate expected by the
source-extensive endpoints from a raw no-overshoot source history, terminality,
and initial activity. This is the direct constructor to use after proving the
real generalized-English transition path has no overshoot at realized dropout
steps.
-/
def theorem8_no_overshoot_terminal_certificate_of_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate where
  localModel := model
  initialState := state
  finalState := finalState
  history := hhist
  terminal := terminal
  initially_active := initially_active

/--
Build the no-overshoot terminal-history certificate directly from an ordinary
generated named-strategy history, provided the source proof supplies the
realized-new-dropout no-overshoot invariant. This is the bridge to use when the
real extensive-form proof naturally produces `StrategyHistory` plus a
step-local timing invariant rather than the strengthened no-overshoot history
object.
-/
def theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      ∀ {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {rank : ℕ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining) state next →
        state.IsActive rank →
        ¬ next.IsActive rank →
        state.clockPrice ≤
          theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  theorem8_no_overshoot_terminal_certificate_of_strategy_history
    model
    (theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot
      model hhist hno_overshoot)
    terminal initially_active

/--
Build the no-overshoot terminal-history certificate from the named source
timing statement rather than an anonymous higher-order premise.
-/
def theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout_statement
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      theorem8RealizedNewDropoutNoOvershootStatement model)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout
    model hhist hno_overshoot terminal initially_active

/--
Raw no-overshoot history to source-extensive completed-rank conclusion using
direct final inactivity on the completed ranks.
-/
theorem theorem8_no_overshoot_strategy_history_source_extensive_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  dsimp
  exact
    theorem8_no_overshoot_terminal_record_source_extensive_completed_rank_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      completedRanks inactive_on_completed hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Raw no-overshoot history to trace-refined source-extensive completed-rank
conclusion using direct final inactivity on the completed ranks.  This is the
review-friendly version: the unique PBE is the named finite `B*` strategy and
also carries the generated history, terminality, exact records, and displayed
completed-rank formulas.
-/
theorem theorem8_no_overshoot_strategy_history_source_extensive_trace_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  dsimp
  exact
    theorem8_no_overshoot_terminal_record_source_extensive_trace_completed_rank_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      completedRanks inactive_on_completed hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Raw no-overshoot history to source-extensive completed-rank conclusion. This
is the one-stop route when the source proof has a concrete no-overshoot
history, terminality, initial activity, and terminal-clock threshold checks for
the displayed completed ranks.
-/
theorem theorem8_no_overshoot_strategy_history_source_extensive_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate
              (model.remaining + 1) (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  dsimp
  exact
    theorem8_no_overshoot_terminal_record_source_extensive_completed_threshold_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      completedRanks hcompleted_threshold_le hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Raw no-overshoot history to trace-refined source-extensive completed-rank
conclusion using terminal-clock threshold checks for the displayed completed
ranks.
-/
theorem theorem8_no_overshoot_strategy_history_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate
              (model.remaining + 1) (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
If a no-overshoot source history starts with all ranks active and ends with no
active ranks, every terminal dropout record is exactly the finite `B*`
threshold.
-/
theorem theorem8_no_overshoot_strategy_history_terminal_records_eq_thresholds
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (hinitial_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    ∀ rank,
      finalState.lastDropout rank =
        some
          (theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1)) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_no_overshoot_strategy_history_terminal_records_eq_thresholds
      model hhist hinitial_active hno_active

/--
If a no-overshoot source history starts with all ranks active and ends with no
active ranks, the terminal dropout-record outcome is the constructed ranked
finite `B*` outcome.
-/
theorem theorem8_no_overshoot_strategy_history_terminal_record_outcome_eq_bstar
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (hinitial_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    paper_theorem8_terminal_dropout_record_outcome finalState =
      paper_theorem8_bstar_ranked_threshold_outcome
        model.value model.clickThroughRate (model.remaining + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_no_overshoot_strategy_history_terminal_record_outcome_eq_bstar
      model hhist hinitial_active hno_active

/--
Clock-disciplined source histories forget to ordinary named-strategy histories.
This is the source-history obligation without the extra exact-record timing
premise.
-/
theorem theorem8_clock_disciplined_strategy_history_to_strategy_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
      (paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining)
      state finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_to_strategy_history
      model hhist

/--
Clock-disciplined source histories imply no-overshoot histories.  The clock
discipline says an advance may not pass any currently active finite `B*`
threshold; with the same condition at the initial state, every later dropout
step has the no-overshoot evidence needed by the exact-record machinery.
-/
theorem theorem8_clock_disciplined_strategy_history_to_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_to_no_overshoot
      model hhist hstate_no_overshoot

/--
Clock-disciplined source histories give exact finite `B*` dropout histories.
This is the source-transition route to exact terminal records.
-/
theorem theorem8_clock_disciplined_strategy_history_to_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_to_exact_drop_history
      model hhist hstate_no_overshoot

/--
Cold-start clock-disciplined source histories induce no-overshoot histories
without a separate initial no-overshoot premise.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_history_to_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_history_to_no_overshoot
      model hvalue_nonneg hclick_mono hhist

/--
Cold-start clock-disciplined source histories give exact finite `B*` dropout
records without a separate initial no-overshoot premise.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_history_to_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_history_to_exact_drop_history
      model hvalue_nonneg hclick_mono hhist

/--
Cold-start clock-disciplined finite traces induce no-overshoot histories
without a separate initial no-overshoot premise.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_to_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_trace_to_no_overshoot
      model hvalue_nonneg hclick_mono htrace

/--
Cold-start clock-disciplined finite traces give exact finite `B*` dropout
records without a separate initial no-overshoot premise.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_to_exact_drop_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState) :
    PaperTheorem8BStarRankedThresholdExactDropHistory
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_trace_to_exact_drop_history
      model hvalue_nonneg hclick_mono htrace

/--
Clock-disciplined finite traces give the exact terminal record for any rank
that starts active and is inactive at the audited final state.
-/
theorem theorem8_clock_disciplined_strategy_trace_final_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hinitial_active : state.IsActive rank)
    (hfinal_inactive : ¬ finalState.IsActive rank) :
    finalState.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_trace_final_record_eq_threshold
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      hinitial_active hfinal_inactive

/--
Cold-start specialization of the clock-disciplined finite-trace per-rank
terminal-record bridge.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_final_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {rank : ℕ}
    (hfinal_inactive : ¬ finalState.IsActive rank) :
    finalState.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_trace_final_record_eq_threshold
      model hvalue_nonneg hclick_mono htrace hfinal_inactive

/--
Clock-disciplined source histories give the exact terminal record for any rank
that starts active and is inactive at the audited final state. This is the
per-rank terminal-record form of the clock-disciplined exact-history bridge.
-/
theorem theorem8_clock_disciplined_strategy_history_final_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    {rank : ℕ}
    (hinitial_active : state.IsActive rank)
    (hfinal_inactive : ¬ finalState.IsActive rank) :
    finalState.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  have hexact :
      PaperTheorem8BStarRankedThresholdExactDropHistory model state finalState :=
    theorem8_clock_disciplined_strategy_history_to_exact_drop_history
      model hhist hstate_no_overshoot
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_history_final_record_eq_threshold
      model hexact hinitial_active hfinal_inactive

/--
Cold-start specialization of the clock-disciplined per-rank terminal-record
bridge. The initial no-overshoot premise is discharged from the paper's
cold-start state and ordered nonnegative finite `B*` threshold assumptions.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_history_final_record_eq_threshold
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state finalState)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {rank : ℕ}
    (hfinal_inactive : ¬ finalState.IsActive rank) :
    finalState.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          model.value model.clickThroughRate (model.remaining + 1)
          (rank + 1)) := by
  exact
    theorem8_clock_disciplined_strategy_history_final_record_eq_threshold
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
            model hvalue_nonneg hclick_mono model.click_pos rank hactive)
      (by rfl) hfinal_inactive

/--
Clock-disciplined source histories supply both the ordinary generated history
and the exact finite `B*` dropout history under the initial no-overshoot
premise.
-/
theorem theorem8_clock_disciplined_strategy_history_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model state finalState := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_clock_disciplined_strategy_history_obligations
      model hhist hstate_no_overshoot

/--
Cold-start clock-disciplined source histories discharge source-extensive
rationality and exact finite `B*` dropout records. Initial no-overshoot is
derived from nonnegative values and monotone, positive click-through rates.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_history_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_history_source_extensive_exact_drop_obligations
      model hvalue_nonneg hclick_mono hhist terminal

/--
Cold-start clock-disciplined source traces discharge source-extensive
rationality and exact finite `B*` dropout records. Initial activity and initial
no-overshoot come from the paper's cold-start state.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_cold_start_clock_disciplined_strategy_trace_source_extensive_exact_drop_obligations
      model hvalue_nonneg hclick_mono htrace terminal

/--
Finite schedule bridge to the clock-disciplined source transition.  A
clock-sorted no-duplicate schedule is clock-disciplined when active ranks
outside the schedule have thresholds above every scheduled threshold.
-/
theorem theorem8_clock_sorted_schedule_to_clock_disciplined_history
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
                  theorem8BStarThresholdBid
                    model.value model.clickThroughRate (model.remaining + 1)
                    (otherRank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_clock_disciplined_strategy_history
      model state ranks hsorted hnodup hinitial_active
      hunscheduled_active_threshold

/--
Finite schedule bridge to the clock-disciplined source transition with the
unscheduled-threshold side condition derived from the final unscheduled-rank
terminality bound.
-/
theorem theorem8_clock_sorted_schedule_to_clock_disciplined_history_of_final_clock_lt_unscheduled
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
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_clock_disciplined_strategy_history_of_final_clock_lt_unscheduled
      model state ranks hsorted hnodup hinitial_active
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Clock-sorted finite schedules also supply the explicit step-by-step
clock-disciplined trace: each scheduled rank advances to its finite `B*`
threshold and then drops under the named strategy.
-/
theorem theorem8_clock_sorted_schedule_to_clock_disciplined_trace
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
                  theorem8BStarThresholdBid
                    model.value model.clickThroughRate (model.remaining + 1)
                    (otherRank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_clock_disciplined_strategy_trace
      model state ranks hsorted hnodup hinitial_active
      hunscheduled_active_threshold

/--
Clock-sorted finite schedules supply the explicit step-by-step clock-disciplined
trace using only the final unscheduled-rank terminality bound for the
unscheduled-threshold side condition.
-/
theorem theorem8_clock_sorted_schedule_to_clock_disciplined_trace_of_final_clock_lt_unscheduled
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
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_to_clock_disciplined_strategy_trace_of_final_clock_lt_unscheduled
      model state ranks hsorted hnodup hinitial_active
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Clock-sorted finite schedules, viewed as explicit clock-disciplined source
traces, discharge the two compact source obligations used downstream:
source-extensive rationality and exact finite `B*` dropout records. The final
terminality check is the usual unscheduled-rank final-clock bound.
-/
theorem theorem8_clock_sorted_schedule_trace_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hnodup : ranks.Nodup)
    (hinitial_active : ∀ rank, rank ∈ ranks → state.IsActive rank)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hunscheduled_active_threshold :
      ∀ scheduledRank,
        scheduledRank ∈ ranks →
          ∀ otherRank,
            otherRank ∉ ranks →
              state.IsActive otherRank →
                paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    model scheduledRank ≤
                  theorem8BStarThresholdBid
                    model.value model.clickThroughRate (model.remaining + 1)
                    (otherRank + 1))
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_trace_source_extensive_exact_drop_obligations
      model state ranks hsorted hnodup hinitial_active
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      (by
        intro scheduledRank hscheduled otherRank hother_not_mem hactive_other
        simpa [theorem8BStarThresholdBid] using
          hunscheduled_active_threshold scheduledRank hscheduled otherRank
            hother_not_mem hactive_other)
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Clock-sorted finite schedules discharge the compact source obligations using
only the final unscheduled-rank terminality bound. The bound implies the
clock-disciplined unscheduled-threshold side condition because every scheduled
threshold is reached by the deterministic final clock.
-/
theorem theorem8_clock_sorted_schedule_trace_source_extensive_exact_drop_obligations_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hnodup : ranks.Nodup)
    (hinitial_active : ∀ rank, rank ∈ ranks → state.IsActive rank)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_trace_source_extensive_exact_drop_obligations_of_final_clock_lt_unscheduled
      model state ranks hsorted hnodup hinitial_active
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Clock-sorted finite schedules discharge the compact source obligations from
the final unscheduled-rank terminality bound alone. The same final-clock check
also derives the initial no-overshoot premise required by the exact finite
`B*` trace.
-/
theorem theorem8_clock_sorted_schedule_trace_source_extensive_exact_drop_obligations_of_final_clock_lt_unscheduled_derive_initial_no_overshoot
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
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_trace_source_extensive_exact_drop_obligations_of_final_clock_lt_unscheduled_derive_initial_no_overshoot
      model state ranks hsorted hnodup hinitial_active
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Cold-start finite schedules discharge the compact source-extensive obligations
through the explicit clock-disciplined trace. Initial activity and initial
no-overshoot are supplied by the paper's cold-start state.
-/
theorem theorem8_cold_start_clock_sorted_schedule_trace_source_extensive_exact_drop_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        ranks)
    (hnodup : ranks.Nodup)
    (hunscheduled_threshold :
      ∀ scheduledRank,
        scheduledRank ∈ ranks →
          ∀ otherRank,
            otherRank ∉ ranks →
              paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  model scheduledRank ≤
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate (model.remaining + 1)
                  (otherRank + 1))
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model paper_theorem8_bstar_ranked_threshold_cold_start_state
            ranks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_cold_start_exact_drop_schedule_clock_sorted_nodup_trace_source_extensive_exact_drop_obligations
      model hvalue_nonneg hclick_mono ranks hsorted hnodup
      (by
        intro scheduledRank hscheduled otherRank hother_not_mem
        simpa [theorem8BStarThresholdBid] using
          hunscheduled_threshold scheduledRank hscheduled otherRank
            hother_not_mem)
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Cold-start clock-sorted finite schedules discharge the compact source
obligations using only the final unscheduled-rank terminality bound. Initial
activity, initial no-overshoot, and the clock-disciplined unscheduled-threshold
side condition are all derived internally.
-/
theorem theorem8_cold_start_clock_sorted_schedule_trace_source_extensive_exact_drop_obligations_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ rank, 0 ≤ model.value rank)
    (hclick_mono : ∀ rank,
      model.clickThroughRate (rank + 1) ≤ model.clickThroughRate rank)
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
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks)
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_cold_start_exact_drop_schedule_clock_sorted_nodup_trace_source_extensive_exact_drop_obligations_of_final_clock_lt_unscheduled
      model hvalue_nonneg hclick_mono ranks hsorted hnodup
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)

/--
Strict-ordered cold-start threshold-sorted append schedules discharge the
compact source-extensive and exact-drop obligations. The paper-facing checks are
the adjacent threshold order, no duplicates, and the last-threshold terminality
bound; Lean derives the cold-start no-overshoot and clock-disciplined source
side condition internally.
-/
theorem theorem8_strict_ordered_cold_start_threshold_sorted_schedule_trace_source_extensive_exact_drop_obligations
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
            theorem8BStarThresholdBid
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
    paper_theorem8_bstar_ranked_threshold_source_extensive_rationality_statement
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          (scheduledPrefix ++ [lastRank]))
        (paper_theorem8_bstar_ranked_threshold_strategy
          localModel.value localModel.clickThroughRate localModel.remaining) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          (scheduledPrefix ++ [lastRank])) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_cold_start_threshold_sorted_append_singleton_trace_source_extensive_exact_drop_obligations
      model scheduledPrefix lastRank hthreshold_sorted hnodup
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hunscheduled_last rank hnot_mem)

/--
Clock-sorted finite schedules end at a clock weakly above their initial clock.
-/
theorem theorem8_clock_sorted_schedule_initial_clock_le_final_clock
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks) :
    state.clockPrice ≤
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state ranks).clockPrice := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_initial_clock_le_final_state_clock_of_clock_sorted
      model state ranks hsorted

/--
Every rank listed in a clock-sorted finite schedule has reached its displayed
finite `B*` threshold by the deterministic final clock.
-/
theorem theorem8_clock_sorted_schedule_threshold_le_final_clock_of_mem
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    {ranks : List ℕ} {rank : ℕ}
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hrank : rank ∈ ranks) :
    theorem8BStarThresholdBid
        model.value model.clickThroughRate (model.remaining + 1)
        (rank + 1) ≤
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state ranks).clockPrice := by
  simpa [theorem8BStarThresholdBid,
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price_le_final_state_clock_of_mem_of_clock_sorted
      model state hsorted hrank

/--
Completed ranks that are included in a clock-sorted finite schedule have all
reached their displayed finite `B*` thresholds by the deterministic final
clock.
-/
theorem theorem8_clock_sorted_schedule_completed_threshold_le_final_clock
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (completedRanks : Finset ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice scheduledRanks)
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks) :
    ∀ rank,
      rank ∈ completedRanks →
        theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) ≤
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state scheduledRanks).clockPrice := by
  intro rank hrank
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_completed_threshold_le_final_state_clock_of_subset_of_clock_sorted
      model state scheduledRanks completedRanks hsorted hsubset rank hrank

/--
The final unscheduled-rank terminality bound also supplies the
clock-disciplined source side condition: every scheduled threshold is below
every unscheduled rank's finite `B*` threshold.
-/
theorem theorem8_clock_sorted_schedule_unscheduled_threshold_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∀ scheduledRank,
      scheduledRank ∈ ranks →
        ∀ otherRank,
          otherRank ∉ ranks →
            state.IsActive otherRank →
              paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  model scheduledRank ≤
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate (model.remaining + 1)
                  (otherRank + 1) := by
  intro scheduledRank hscheduled otherRank hother_not_mem hactive
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_active_threshold_of_final_clock_lt_unscheduled
      model state ranks hsorted
      (by
        intro rank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled rank hnot_mem)
      scheduledRank hscheduled otherRank hother_not_mem hactive

/--
The final unscheduled-rank terminality bound also supplies the initial
no-overshoot condition for every active rank at the schedule source state.
-/
theorem theorem8_clock_sorted_schedule_initial_no_overshoot_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hterminal_unscheduled :
      ∀ rank,
        rank ∉ ranks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state ranks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1)) :
    ∀ rank,
      state.IsActive rank →
        state.clockPrice ≤
          theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1) := by
  intro rank hactive
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_initial_no_overshoot_of_clock_sorted_final_clock_lt_unscheduled
      model state ranks hsorted
      (by
        intro otherRank hnot_mem
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled otherRank hnot_mem)
      rank hactive

/--
Clock-sorted finite schedules supply both the named-strategy reachability
history and the exact finite `B*` dropout history for the deterministic
schedule final state.
-/
theorem theorem8_clock_sorted_schedule_history_obligations
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model state.clockPrice ranks)
    (hnodup : ranks.Nodup)
    (hinitial_active : ∀ rank, rank ∈ ranks → state.IsActive rank) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks) ∧
      PaperTheorem8BStarRankedThresholdExactDropHistory model state
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model state ranks) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted_nodup_history_obligations
      model state ranks hsorted hnodup hinitial_active

/--
Singleton schedule shortcut for the clock-disciplined source transition.
-/
theorem theorem8_singleton_schedule_to_clock_disciplined_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (rank : ℕ)
    (hclock :
      state.clockPrice ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model rank)
    (hactive : state.IsActive rank)
    (hunscheduled_active_threshold :
      ∀ otherRank,
        otherRank ≠ rank →
          state.IsActive otherRank →
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                model rank ≤
              theorem8BStarThresholdBid
                model.value model.clickThroughRate (model.remaining + 1)
                (otherRank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state [rank]) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_singleton_to_clock_disciplined_strategy_history
      model state rank hclock hactive hunscheduled_active_threshold

/--
Two-rank schedule shortcut for the clock-disciplined source transition.
-/
theorem theorem8_pair_schedule_to_clock_disciplined_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (rank nextRank : ℕ)
    (hclock :
      state.clockPrice ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model rank)
    (hnext :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model rank ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model nextRank)
    (hne : rank ≠ nextRank)
    (hactive_rank : state.IsActive rank)
    (hactive_next : state.IsActive nextRank)
    (hunscheduled_active_threshold :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            state.IsActive otherRank →
              paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  model nextRank ≤
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate (model.remaining + 1)
                  (otherRank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state [rank, nextRank]) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_pair_to_clock_disciplined_strategy_history
      model state rank nextRank hclock hnext hne hactive_rank hactive_next
      hunscheduled_active_threshold

/--
Singleton schedule shortcut with the unscheduled-threshold side condition
derived from final-clock terminality.
-/
theorem theorem8_singleton_schedule_to_clock_disciplined_history_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (rank : ℕ)
    (hclock :
      state.clockPrice ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model rank)
    (hactive : state.IsActive rank)
    (hterminal_unscheduled :
      ∀ otherRank,
        otherRank ≠ rank →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model state [rank]).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (otherRank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state [rank]) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_singleton_to_clock_disciplined_strategy_history_of_final_clock_lt_unscheduled
      model state rank hclock hactive
      (by
        intro otherRank hne
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled otherRank hne)

/--
Two-rank schedule shortcut with the unscheduled-threshold side condition
derived from final-clock terminality.
-/
theorem theorem8_pair_schedule_to_clock_disciplined_history_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (state : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (rank nextRank : ℕ)
    (hclock :
      state.clockPrice ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model rank)
    (hnext :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model rank ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          model nextRank)
    (hne : rank ≠ nextRank)
    (hactive_rank : state.IsActive rank)
    (hactive_next : state.IsActive nextRank)
    (hterminal_unscheduled :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
              model state [rank, nextRank]).clockPrice <
              theorem8BStarThresholdBid
                model.value model.clickThroughRate (model.remaining + 1)
                (otherRank + 1)) :
    PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
      model state
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model state [rank, nextRank]) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_pair_to_clock_disciplined_strategy_history_of_final_clock_lt_unscheduled
      model state rank nextRank hclock hnext hne hactive_rank hactive_next
      (by
        intro otherRank hne_rank hne_next
        simpa [theorem8BStarThresholdBid] using
          hterminal_unscheduled otherRank hne_rank hne_next)

private def theorem8FreshUnscheduledRank : List ℕ → ℕ
  | [] => 0
  | rank :: tail => max (rank + 1) (theorem8FreshUnscheduledRank tail)

private theorem theorem8_mem_lt_fresh_unscheduled_rank
    {ranks : List ℕ} {rank : ℕ}
    (hrank : rank ∈ ranks) :
    rank < theorem8FreshUnscheduledRank ranks := by
  induction ranks with
  | nil =>
      cases hrank
  | cons head tail ih =>
      rw [List.mem_cons] at hrank
      dsimp [theorem8FreshUnscheduledRank]
      rcases hrank with hhead | htail
      · subst rank
        exact lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left (head + 1) (theorem8FreshUnscheduledRank tail))
      · exact lt_of_lt_of_le (ih htail)
          (Nat.le_max_right (head + 1) (theorem8FreshUnscheduledRank tail))

private theorem theorem8_fresh_unscheduled_rank_not_mem
    (ranks : List ℕ) :
    theorem8FreshUnscheduledRank ranks ∉ ranks := by
  intro hrank
  exact (Nat.lt_irrefl (theorem8FreshUnscheduledRank ranks))
    (theorem8_mem_lt_fresh_unscheduled_rank hrank)

/--
Finite cold-start schedules over the current `ℕ`-rank model cannot prove the
all-terminal premise: after any finite no-duplicate exact-drop schedule, some
unscheduled rank remains active.  This is why the finite paper-checking route
uses completed-rank conclusions, while all-terminal VCG wrappers need either an
external all-ranks-inactive premise or a future finite-bidder source model.
-/
theorem theorem8_cold_start_clock_sorted_finite_schedule_leaves_active_unscheduled_rank
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (ranks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        ranks)
    (hnodup : ranks.Nodup) :
    ∃ rank,
      rank ∉ ranks ∧
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model paper_theorem8_bstar_ranked_threshold_cold_start_state
          ranks).IsActive rank := by
  let rank := theorem8FreshUnscheduledRank ranks
  have hnot_mem : rank ∉ ranks :=
    theorem8_fresh_unscheduled_rank_not_mem ranks
  refine ⟨rank, hnot_mem, ?_⟩
  exact
    (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_active_iff_not_mem_of_clock_sorted_nodup
      model paper_theorem8_bstar_ranked_threshold_cold_start_state ranks
      hsorted hnodup (fun rank => by rfl) rank).mpr hnot_mem

/--
Finite-active cold-start terminality helper. If the source instance has an
explicit finite active set and the exact-drop schedule covers exactly that set,
then the deterministic final state has no active ranks left. This is the
finite-source route; unscheduled inactive ranks keep their initial placeholder
records, so this is not by itself the all-rank constructed-`B*` outcome proof.
-/
theorem theorem8_finite_active_cold_start_clock_sorted_schedule_no_active
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (inactivePrice : ℝ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_cold_start_state
          activeRanks inactivePrice).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hcover : ∀ rank, rank ∈ activeRanks ↔ rank ∈ scheduledRanks) :
    ∀ rank,
      ¬ (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model
          (paper_theorem8_bstar_ranked_threshold_finite_active_cold_start_state
            activeRanks inactivePrice)
          scheduledRanks).IsActive rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_no_active_of_finite_active_cold_start_covers
      model activeRanks inactivePrice scheduledRanks hsorted hnodup hcover

/--
Initial-state ledger for the exact-record finite-active source instance: the
listed finite ranks are active, and every unlisted rank already carries its
exact finite `B*` dropout record.
-/
theorem theorem8_finite_active_exact_record_cold_start_state_ledger
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (rank : ℕ) :
    ((paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      model activeRanks).IsActive rank ↔ rank ∈ activeRanks) ∧
      (rank ∉ activeRanks →
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model activeRanks).lastDropout rank =
          some
            (paper_theorem8_bstar_threshold_bid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))) := by
  exact
    ⟨paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_active_iff
        model activeRanks rank,
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_lastDropout_of_not_mem
        model activeRanks⟩

/--
Exact-record finite-active full-outcome helper. If the finite source instance
starts with exact finite-`B*` records for already-inactive ranks and the
clock-sorted exact-drop schedule covers exactly the active ranks, then the
terminal dropout-record outcome is the constructed ranked `B*` outcome for all
ranks.
-/
theorem theorem8_finite_active_exact_record_cold_start_terminal_record_outcome_eq_bstar
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model activeRanks).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hcover : ∀ rank, rank ∈ activeRanks ↔ rank ∈ scheduledRanks) :
    paper_theorem8_terminal_dropout_record_outcome
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model
          (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
            model activeRanks)
          scheduledRanks) =
      paper_theorem8_bstar_ranked_threshold_outcome
        model.value model.clickThroughRate (model.remaining + 1) := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_terminal_record_outcome_eq_bstar_of_finite_active_exact_record_cold_start_covers
      model activeRanks scheduledRanks hsorted hnodup hcover

/--
The same exact-record finite-active source instance also has no active ranks
left after the covering exact-drop schedule.
-/
theorem theorem8_finite_active_exact_record_cold_start_clock_sorted_schedule_no_active
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model activeRanks).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hcover : ∀ rank, rank ∈ activeRanks ↔ rank ∈ scheduledRanks) :
    ∀ rank,
      ¬ (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
          model
          (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
            model activeRanks)
          scheduledRanks).IsActive rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_no_active_of_finite_active_exact_record_cold_start_covers
      model activeRanks scheduledRanks hsorted hnodup hcover

/--
Exact-record finite-active source-game endpoint. For the state-based
terminal-record source game, the covering exact-drop schedule gives a unique
PBE whose terminal-record outcome equals the constructed ranked `B*` outcome.
-/
theorem theorem8_finite_active_exact_record_source_game_unique_pbe_outcome_eq_bstar
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model activeRanks).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hcover : ∀ rank, rank ∈ activeRanks ↔ rank ∈ scheduledRanks) :
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        model activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states
        model initialState finalState
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome := by
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states_exists_unique_pbe_with_outcome_eq_vcg_of_finite_active_exact_record_cold_start_covers
      model activeRanks scheduledRanks hsorted hnodup hcover

/--
Bundled exact-record finite-active source-game endpoint. This adds the
component slot/payment equalities and bidder utility equalities to the unique
PBE terminal-record outcome conclusion.
-/
theorem theorem8_finite_active_exact_record_source_game_full_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model activeRanks).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hcover : ∀ rank, rank ∈ activeRanks ↔ rank ∈ scheduledRanks) :
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        model activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states
        model initialState finalState
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome ∧
          (∀ rank,
            (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
              (G.outcomeOf strategy).paymentPerClick rank =
                G.vcgOutcome.paymentPerClick rank) ∧
            ∀ bidder,
              (G.outcomeOf strategy).utility G.environment G.values bidder =
                G.vcgOutcome.utility G.environment G.values bidder := by
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states_exists_unique_pbe_with_all_terminal_vcg_conclusion_of_finite_active_exact_record_cold_start_covers
      model activeRanks scheduledRanks hsorted hnodup hcover

/--
Trace-refined exact-record finite-active source-game endpoint. The unique PBE
is the named finite-`B*` strategy and carries the generated strategy history,
terminality, exact-drop history, outcome equality, rankwise slot/payment
equality, and bidder utility equality.
-/
theorem theorem8_finite_active_exact_record_source_game_trace_full_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (activeRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model activeRanks).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hcover : ∀ rank, rank ∈ activeRanks ↔ rank ∈ scheduledRanks) :
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        model activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states
        model initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  model initialState finalState ∧
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
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states_exists_unique_pbe_with_trace_full_vcg_conclusion_of_finite_active_exact_record_cold_start_covers
      model activeRanks scheduledRanks hsorted hnodup hcover

/--
Schedule-only version of
`theorem8_finite_active_exact_record_source_game_trace_full_vcg_conclusion`.
The finite active set is `scheduledRanks.toFinset`, so the caller only checks
clock-sortedness and no duplicates.
-/
theorem theorem8_finite_active_exact_record_schedule_trace_full_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          model scheduledRanks.toFinset).clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup) :
    let activeRanks := scheduledRanks.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        model activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        model initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states
        model initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  model initialState finalState ∧
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
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states_exists_unique_pbe_with_trace_full_vcg_conclusion_of_finite_active_exact_record_schedule
      model scheduledRanks hsorted hnodup

/--
Strict-ordered threshold-sorted schedule version of the finite exact-record
trace endpoint. Under the paper's strict ordered assumptions, reviewers check
adjacent threshold-sortedness and no duplicates; the initial `-1` clock
inequality is discharged automatically.
-/
theorem theorem8_strict_ordered_finite_active_exact_record_schedule_trace_full_vcg_conclusion_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (scheduledRanks : List ℕ)
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := scheduledRanks.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  localModel initialState finalState ∧
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
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup

/--
Source-extensive version of
`theorem8_strict_ordered_finite_active_exact_record_schedule_trace_full_vcg_conclusion_of_threshold_sorted`.
The PBE predicate itself includes generated history and terminality for the
finite exact-record state-based source game.
-/
theorem theorem8_strict_ordered_finite_active_exact_record_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (scheduledRanks : List ℕ)
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := scheduledRanks.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  localModel initialState finalState ∧
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
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup

/--
Belief-explicit source-extensive version of the finite exact-record schedule
endpoint. The PBE witness carries a concrete source-extensive belief containing
the generated history and terminality proof.
-/
theorem theorem8_strict_ordered_finite_active_exact_record_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (scheduledRanks : List ℕ)
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := scheduledRanks.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState scheduledRanks
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  localModel initialState finalState ∧
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
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup

/-- Translate a finite displayed bidder/rank schedule into the natural-rank
schedule used by the current Theorem 8 model. -/
def theorem8FinScheduleRanks {n : ℕ} (scheduledRanks : List (Fin n)) : List ℕ :=
  scheduledRanks.map (fun rank => rank.val)

/-- The `Fin n` schedule translation preserves no-duplicate schedules. -/
theorem theorem8FinScheduleRanks_nodup {n : ℕ}
    {scheduledRanks : List (Fin n)}
    (hnodup : scheduledRanks.Nodup) :
    (theorem8FinScheduleRanks scheduledRanks).Nodup := by
  simpa [theorem8FinScheduleRanks] using hnodup.map Fin.val_injective

/--
Finite-index completion check. If the displayed `Fin n` schedule is
threshold-sorted and has no duplicates, then the exact-record finite-active
source instance generated from that schedule has no active ranks after the
schedule is executed.
-/
theorem theorem8_strict_ordered_fin_schedule_exact_record_final_state_no_active_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    ∀ rank, ¬ finalState.IsActive rank := by
  dsimp
  let rankSchedule := theorem8FinScheduleRanks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  have hnodup_nat : rankSchedule.Nodup := by
    simpa [rankSchedule] using theorem8FinScheduleRanks_nodup hnodup
  have hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        localModel
        (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
          localModel rankSchedule.toFinset).clockPrice
        rankSchedule := by
    simpa [localModel, rankSchedule,
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state,
      paper_theorem8_bstar_ranked_threshold_cold_start_state] using
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_of_threshold_sorted
        model rankSchedule hthreshold_sorted)
  exact
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state_no_active_of_finite_active_exact_record_cold_start_covers
      localModel rankSchedule.toFinset rankSchedule hsorted hnodup_nat
      (by
        intro rank
        simp)

/--
Complete finite-index schedule check. If every displayed `Fin n` rank appears
in the schedule, then each displayed rank starts active in the exact-record
finite source state and ends inactive after the threshold-sorted schedule is
executed.
-/
theorem theorem8_strict_ordered_complete_fin_schedule_displayed_ranks_active_then_inactive_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup)
    (hcomplete : ∀ rank : Fin n, rank ∈ scheduledRanks) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    ∀ rank : Fin n,
      initialState.IsActive rank.val ∧ ¬ finalState.IsActive rank.val := by
  dsimp
  let rankSchedule := theorem8FinScheduleRanks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  have hfinal :
      ∀ rank, ¬ finalState.IsActive rank := by
    simpa [rankSchedule, localModel, activeRanks, initialState, finalState] using
      theorem8_strict_ordered_fin_schedule_exact_record_final_state_no_active_of_threshold_sorted
        model scheduledRanks hthreshold_sorted hnodup
  intro rank
  have hmem_rankSchedule : rank.val ∈ rankSchedule := by
    simpa [rankSchedule, theorem8FinScheduleRanks] using
      (List.mem_map.mpr ⟨rank, hcomplete rank, rfl⟩)
  have hinitial : initialState.IsActive rank.val := by
    exact
      (paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_active_iff
        localModel activeRanks rank.val).mpr
        (by
          simpa [activeRanks] using hmem_rankSchedule)
  exact ⟨hinitial, hfinal rank.val⟩

/--
Finite-index schedule wrapper for the source-extensive finite exact-record
endpoint. Reviewers can write the displayed finite schedule as `List (Fin n)`;
Lean then translates it to the natural-rank schedule used internally.
-/
theorem theorem8_strict_ordered_fin_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  localModel initialState finalState ∧
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
  dsimp
  have hnodup_nat : (theorem8FinScheduleRanks scheduledRanks).Nodup := by
    simpa [theorem8FinScheduleRanks] using hnodup.map Fin.val_injective
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model (theorem8FinScheduleRanks scheduledRanks) hthreshold_sorted
      hnodup_nat

/--
Named-strategy trace extracted from the finite-index source-extensive
endpoint. This is the compact source-checker statement that the displayed
finite schedule produces a PBE for the named finite `B*` strategy, with the
generated history, terminality, and exact-drop history visible directly.
-/
theorem theorem8_strict_ordered_fin_schedule_source_extensive_named_pbe_trace_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    G.PerfectBayesianEquilibrium namedStrategy ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        namedStrategy initialState finalState ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
          namedStrategy finalState ∧
          PaperTheorem8BStarRankedThresholdExactDropHistory
            localModel initialState finalState := by
  dsimp
  let rankSchedule := theorem8FinScheduleRanks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
      localModel initialState finalState
  let namedStrategy :=
    paper_theorem8_bstar_ranked_threshold_strategy
      localModel.value localModel.clickThroughRate localModel.remaining
  have hbase :=
    theorem8_strict_ordered_fin_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup
  rcases hbase.exists with
    ⟨strategy, hpbe, hnamed, hhistory, hterminal, hexact, _hout, _hrank, _hutil⟩
  subst strategy
  exact ⟨hpbe, hhistory, hterminal, hexact⟩

/--
Finite-index source-extensive displayed-formula wrapper. In addition to the
finite-source PBE statement, this exposes the rankwise slot and finite `B*`
payment formula directly for every displayed `Fin n` rank.
-/
theorem theorem8_strict_ordered_fin_schedule_source_extensive_displayed_rank_formulas_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          ∀ rank : Fin n,
            (G.outcomeOf strategy).slotOf rank.val = some rank.val ∧
              (G.outcomeOf strategy).paymentPerClick rank.val =
                paper_theorem8_bstar_threshold_bid
                  localModel.value localModel.clickThroughRate
                  (localModel.remaining + 1) (rank.val + 1) := by
  dsimp
  let rankSchedule := theorem8FinScheduleRanks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
      localModel initialState finalState
  let namedStrategy :=
    paper_theorem8_bstar_ranked_threshold_strategy
      localModel.value localModel.clickThroughRate localModel.remaining
  have hbase :=
    theorem8_strict_ordered_fin_schedule_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup
  dsimp [rankSchedule, localModel, activeRanks, initialState, finalState, G,
    namedStrategy] at hbase
  rcases hbase with ⟨strategy, hstrategy, _hunique⟩
  rcases hstrategy with
    ⟨hpbe, hnamed, _hhist, _hterminal, _hexact, hout, _hslotpay, _hutil⟩
  refine ⟨strategy, ?_, ?_⟩
  · refine ⟨hpbe, hnamed, ?_⟩
    intro rank
    constructor
    · exact
        congrArg (fun outcome => outcome.slotOf rank.val) hout
    · exact
        congrArg (fun outcome => outcome.paymentPerClick rank.val) hout
  · intro other hother
    exact hother.2.1.trans hnamed.symm

/--
Finite-index schedule wrapper for the belief-explicit finite exact-record
endpoint. Reviewers can write the displayed finite schedule as `List (Fin n)`;
Lean then translates it to the natural-rank schedule used internally.
-/
theorem theorem8_strict_ordered_fin_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  localModel initialState finalState ∧
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
  dsimp
  have hnodup_nat : (theorem8FinScheduleRanks scheduledRanks).Nodup := by
    simpa [theorem8FinScheduleRanks] using hnodup.map Fin.val_injective
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_finite_active_exact_record_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model (theorem8FinScheduleRanks scheduledRanks) hthreshold_sorted
      hnodup_nat

/--
Named-strategy trace extracted from the finite-index belief-explicit
source-extensive endpoint. This is the compact check that the displayed
finite schedule produces a PBE for the named finite `B*` strategy, with the
generated history, terminality, and exact-drop history visible directly.
-/
theorem theorem8_strict_ordered_fin_schedule_belief_source_extensive_named_pbe_trace_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    G.PerfectBayesianEquilibrium namedStrategy ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        namedStrategy initialState finalState ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
          namedStrategy finalState ∧
          PaperTheorem8BStarRankedThresholdExactDropHistory
            localModel initialState finalState := by
  dsimp
  let rankSchedule := theorem8FinScheduleRanks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
      localModel initialState finalState
  let namedStrategy :=
    paper_theorem8_bstar_ranked_threshold_strategy
      localModel.value localModel.clickThroughRate localModel.remaining
  have hbase :=
    theorem8_strict_ordered_fin_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup
  rcases hbase.exists with
    ⟨strategy, hpbe, hnamed, hhistory, hterminal, hexact, _hout, _hrank, _hutil⟩
  subst strategy
  exact ⟨hpbe, hhistory, hterminal, hexact⟩

/--
Finite-index displayed-formula wrapper. In addition to the belief-explicit
finite-source PBE statement, this exposes the rankwise slot and finite `B*`
payment formula directly for every displayed `Fin n` rank.
-/
theorem theorem8_strict_ordered_fin_schedule_belief_source_extensive_displayed_rank_formulas_of_threshold_sorted
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    {n : ℕ} (scheduledRanks : List (Fin n))
    (hthreshold_sorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        (theorem8FinScheduleRanks scheduledRanks))
    (hnodup : scheduledRanks.Nodup) :
    let rankSchedule := theorem8FinScheduleRanks scheduledRanks
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let activeRanks := rankSchedule.toFinset
    let initialState :=
      paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
        localModel activeRanks
    let finalState :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
        localModel initialState rankSchedule
    let G :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
        localModel initialState finalState
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          ∀ rank : Fin n,
            (G.outcomeOf strategy).slotOf rank.val = some rank.val ∧
              (G.outcomeOf strategy).paymentPerClick rank.val =
                paper_theorem8_bstar_threshold_bid
                  localModel.value localModel.clickThroughRate
                  (localModel.remaining + 1) (rank.val + 1) := by
  dsimp
  let rankSchedule := theorem8FinScheduleRanks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
      localModel initialState finalState
  let namedStrategy :=
    paper_theorem8_bstar_ranked_threshold_strategy
      localModel.value localModel.clickThroughRate localModel.remaining
  have hbase :=
    theorem8_strict_ordered_fin_schedule_belief_source_extensive_trace_full_vcg_conclusion_of_threshold_sorted
      model scheduledRanks hthreshold_sorted hnodup
  dsimp [rankSchedule, localModel, activeRanks, initialState, finalState, G,
    namedStrategy] at hbase
  rcases hbase with ⟨strategy, hstrategy, _hunique⟩
  rcases hstrategy with
    ⟨hpbe, hnamed, _hhist, _hterminal, _hexact, hout, _hslotpay, _hutil⟩
  refine ⟨strategy, ?_, ?_⟩
  · refine ⟨hpbe, hnamed, ?_⟩
    intro rank
    constructor
    · exact
        congrArg (fun outcome => outcome.slotOf rank.val) hout
    · exact
        congrArg (fun outcome => outcome.paymentPerClick rank.val) hout
  · intro other hother
    exact hother.2.1.trans hnamed.symm

/--
Meaning of the finite exact-record source-extensive PBE predicate: behavioral
one-step optimality, threshold tie-breaking, generated history, and terminality.
-/
theorem theorem8_source_extensive_state_game_pbe_iff_one_step_tiebreak_history_terminal
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
      model initialState finalState).PerfectBayesianEquilibrium strategy ↔
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
          model.clickThroughRate model.value model.remaining strategy ∧
        paper_theorem8_bstar_ranked_threshold_drop_at_threshold_statement
          model.clickThroughRate model.value model.remaining strategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
            strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
              strategy finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states_pbe_iff_one_step_best_response_drop_at_threshold_history_terminal
      model initialState finalState strategy

/--
Equivalent human-facing reading of the finite exact-record source-extensive PBE
predicate: a PBE is exactly the named finite `B*` strategy, plus generated
history and terminality.
-/
theorem theorem8_source_extensive_state_game_pbe_iff_named_strategy_history_terminal
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
      model initialState finalState).PerfectBayesianEquilibrium strategy ↔
      strategy =
          paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
          strategy initialState finalState ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
            strategy finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states_pbe_iff_named_strategy_history_terminal
      model initialState finalState strategy

/--
Meaning of the belief-explicit finite exact-record source-extensive PBE
predicate. The same four obligations are checked, with generated history and
terminality carried by the PBE belief witness.
-/
theorem theorem8_belief_source_extensive_state_game_pbe_iff_one_step_tiebreak_history_terminal
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
      model initialState finalState).PerfectBayesianEquilibrium strategy ↔
      paper_theorem8_bstar_ranked_threshold_one_step_best_response_statement
          model.clickThroughRate model.value model.remaining strategy ∧
        paper_theorem8_bstar_ranked_threshold_drop_at_threshold_statement
          model.clickThroughRate model.value model.remaining strategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
            strategy initialState finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
              strategy finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states_pbe_iff_one_step_best_response_drop_at_threshold_history_terminal
      model initialState finalState strategy

/--
Equivalent human-facing reading of the belief-explicit finite exact-record PBE
predicate: a PBE is exactly the named finite `B*` strategy, plus generated
history and terminality carried by the belief witness.
-/
theorem theorem8_belief_source_extensive_state_game_pbe_iff_named_strategy_history_terminal
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states
      model initialState finalState).PerfectBayesianEquilibrium strategy ↔
      strategy =
          paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining ∧
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
          strategy initialState finalState ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
            strategy finalState := by
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_of_states_pbe_iff_named_strategy_history_terminal
      model initialState finalState strategy

/--
Build the no-overshoot terminal-history certificate used by the
source-extensive endpoints from a clock-disciplined terminal history.
-/
def theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_disciplined_strategy_history
    model hhist
    (by
      intro rank hactive
      simpa [theorem8BStarThresholdBid] using
        hstate_no_overshoot rank hactive)
    terminal initially_active

/--
Cold-start no-overshoot terminal-history certificate from a
clock-disciplined source history. The paper cold-start state discharges both
initial activity and the initial no-overshoot premise.
-/
def theorem8_no_overshoot_terminal_certificate_of_cold_start_clock_disciplined_history
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_cold_start_clock_disciplined_strategy_history
    model hvalue_nonneg hclick_mono hhist terminal

/--
Build the no-overshoot terminal-history certificate from a finite trace of
clock-disciplined source steps. This is the preferred interface when source
semantics prove clock discipline one transition at a time.
-/
def theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
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
    model htrace
    (by
      intro rank hactive
      simpa [theorem8BStarThresholdBid] using
        hstate_no_overshoot rank hactive)
    terminal initially_active

/--
Cold-start no-overshoot terminal-history certificate from a finite trace of
clock-disciplined source steps. The initial no-overshoot and initial-activity
premises are discharged internally from the paper's cold-start state.
-/
def theorem8_no_overshoot_terminal_certificate_of_cold_start_clock_disciplined_trace
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState) :
    PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate :=
  paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_cold_start_clock_disciplined_strategy_trace
    model hvalue_nonneg hclick_mono htrace terminal

/--
Clock-disciplined terminal-history source-extensive endpoint.  This is the
direct paper-facing route from a clock-disciplined terminal history to the
completed-rank source-extensive conclusion, without manually building the
intermediate no-overshoot certificate.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Trace-refined clock-disciplined terminal-history source-extensive endpoint with
the direct completed-rank inactivity premise.  Use this when the source proof
has already identified a finite set of dropped/completed ranks.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_trace_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_no_overshoot_terminal_record_source_extensive_trace_completed_rank_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active)
      completedRanks inactive_on_completed hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Trace-refined clock-disciplined terminal-history source-extensive endpoint.
This is the direct paper-facing route from a clock-disciplined terminal history
to the completed-rank conclusion, while also exposing the named finite `B*`
strategy, generated history, terminality, and exact finite `B*` dropout trace.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Trace-level clock-disciplined source-extensive endpoint.  This is the direct
paper-facing route from a finite clock-disciplined source trace to the
completed-rank conclusion, while also exposing the named finite `B*` strategy,
generated history, terminality, and exact finite `B*` dropout trace.
-/
theorem theorem8_clock_disciplined_strategy_trace_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_clock_disciplined_strategy_trace
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Cold-start source-extensive clock-disciplined trace endpoint. The PBE checker
still carries the generated history and terminality proof, but the initial
no-overshoot and initial-activity premises are derived from the cold-start
state.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_source_extensive_trace_completed_threshold_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) completedRanks
      hcompleted_threshold_le hvalue_nonneg hvalue_mono hclick_mono
      model.click_pos

/--
Cold-start trace-level source-extensive endpoint.  The finite
clock-disciplined source trace supplies the generated source path; Lean derives
the cold-start initial no-overshoot and initial-activity premises internally.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminal (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    theorem8_clock_disciplined_strategy_trace_source_extensive_trace_completed_threshold_conclusion
      model htrace
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) completedRanks
      hcompleted_threshold_le hvalue_nonneg hvalue_mono hclick_mono
      model.click_pos

/--
Cold-start source-extensive clock-disciplined trace endpoint with direct
completed-rank inactivity.  This is the finite-rank paper-checking form for a
source history that starts at the paper cold-start state.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_trace_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_source_extensive_trace_completed_rank_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) completedRanks inactive_on_completed
      hvalue_nonneg hvalue_mono hclick_mono model.click_pos

/--
Belief-explicit clock-disciplined source-extensive completed-rank endpoint.
This is the same clock-disciplined terminal-history route as above, but the
PBE belief carries the generated history and terminality proof and consistency
checks that they belong to the strategy under review.
-/
theorem theorem8_clock_disciplined_terminal_history_belief_source_extensive_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Trace-refined belief-explicit clock-disciplined source-extensive
completed-rank endpoint.  The unique PBE witness is the named finite `B*`
strategy, carries a consistent belief with generated history and terminality,
and satisfies the displayed completed-rank paper formula.
-/
theorem theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Cold-start belief-explicit clock-disciplined trace endpoint. The generated
history and terminality proof remain inside the belief object, while the
cold-start state discharges the initial no-overshoot and initial-activity
premises.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) completedRanks
      hcompleted_threshold_le hvalue_nonneg hvalue_mono hclick_mono
      model.click_pos

/--
Clock-disciplined all-terminal source-extensive endpoint.  A terminal
clock-disciplined history with no active ranks left yields a unique PBE whose
terminal-record outcome is the VCG target.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_outcome_eq_vcg
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome := by
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_outcome_eq_vcg_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Clock-disciplined all-terminal source-extensive component endpoint.  A terminal
clock-disciplined history with no active ranks left yields a unique PBE whose
slot/payment components match the VCG target.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_slot_payment_eq_vcg
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
            (G.outcomeOf strategy).paymentPerClick rank =
              G.vcgOutcome.paymentPerClick rank := by
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_slot_payment_eq_vcg_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Clock-disciplined all-terminal source-extensive payoff endpoint.  A terminal
clock-disciplined history with no active ranks left yields a unique PBE whose
bidder utilities equal the VCG utilities.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_utility_eq_vcg
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ bidder,
          (G.outcomeOf strategy).utility G.environment G.values bidder =
            G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_utility_eq_vcg_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Clock-disciplined all-terminal source-extensive full endpoint.  A terminal
clock-disciplined history with no active ranks left yields a unique PBE with
VCG outcome equality, VCG slot/payment components, and VCG bidder utilities.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome ∧
          (∀ rank,
            (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
              (G.outcomeOf strategy).paymentPerClick rank =
                G.vcgOutcome.paymentPerClick rank) ∧
            ∀ bidder,
              (G.outcomeOf strategy).utility G.environment G.values bidder =
                G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_all_terminal_vcg_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Clock-disciplined all-terminal belief-explicit endpoint.  The
clock-disciplined terminal history builds the no-overshoot terminal certificate,
then the non-vacuous belief checker returns unique PBE, VCG outcome equality,
rankwise slot/payment equality, and bidder utility equality.
-/
theorem theorem8_clock_disciplined_terminal_history_belief_source_extensive_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome ∧
          (∀ rank,
            (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
              (G.outcomeOf strategy).paymentPerClick rank =
                G.vcgOutcome.paymentPerClick rank) ∧
            ∀ bidder,
              (G.outcomeOf strategy).utility G.environment G.values bidder =
                G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordBeliefSourceExtensiveGame,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_belief_source_extensive_all_terminal_vcg_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active)
      hno_active

/--
Trace-refined clock-disciplined belief-explicit endpoint.  A terminal
clock-disciplined history yields the unique PBE in the non-vacuous belief
checker, the named finite `B*` strategy identity, the generated source history,
terminality, exact dropout records, and the bundled all-terminal VCG
conclusion.
-/
theorem theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
  simpa [terminalRecordBeliefSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Trace-level clock-disciplined belief-explicit all-terminal endpoint.  The
finite source trace is packaged directly into the non-vacuous belief checker,
with generated history, terminality, exact dropout records, and the bundled VCG
conclusion exposed in the unique PBE witness.
-/
theorem theorem8_clock_disciplined_strategy_trace_belief_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminal initially_active
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
  simpa [terminalRecordBeliefSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_clock_disciplined_strategy_trace
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Trace-refined clock-disciplined all-terminal source-extensive endpoint.  The
clock-disciplined terminal history yields the named finite `B*` PBE, generated
history, terminality, exact finite `B*` dropout trace, and bundled all-terminal
VCG conclusion.
-/
theorem theorem8_clock_disciplined_terminal_history_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_clock_disciplined_terminal_history
      model hhist
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Trace-level clock-disciplined all-terminal source-extensive endpoint.  The
finite source trace is packaged directly into the source-extensive checker,
with generated history, terminality, exact dropout records, and the bundled VCG
conclusion exposed in the unique PBE witness.
-/
theorem theorem8_clock_disciplined_strategy_trace_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_clock_disciplined_strategy_trace
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          hstate_no_overshoot rank hactive)
      terminal initially_active hno_active

/--
Cold-start all-terminal source-extensive endpoint.  Starting from the paper's
initial auction state, Lean derives the initial no-overshoot and initial
activity obligations internally; the remaining source-side obligations are the
clock-disciplined generated history, terminality, and that no ranks remain
active.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let G := terminalRecordSourceExtensiveGame terminalCert
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome ∧
          (∀ rank,
            (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
              (G.outcomeOf strategy).paymentPerClick rank =
                G.vcgOutcome.paymentPerClick rank) ∧
            ∀ bidder,
              (G.outcomeOf strategy).utility G.environment G.values bidder =
                G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_source_extensive_all_terminal_vcg_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) hno_active

/--
Cold-start belief-explicit all-terminal trace endpoint.  The unique PBE witness
is the named finite `B*` strategy, with a generated history, terminality proof,
exact finite `B*` dropout trace, and the bundled all-terminal VCG conclusion.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
  simpa [terminalRecordBeliefSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) hno_active

/--
Cold-start source-extensive all-terminal trace endpoint.  This is the same
cold-start bridge as the belief-explicit checker, but for the source-extensive
game without exposing beliefs in the statement.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_source_extensive_trace_all_terminal_vcg_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) hno_active

/--
Cold-start belief-explicit all-terminal endpoint from an explicit finite
clock-disciplined source trace. Initial activity and initial no-overshoot are
derived from the paper cold-start state.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_belief_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminal (fun rank => by rfl)
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
  simpa [terminalRecordBeliefSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    theorem8_clock_disciplined_strategy_trace_belief_source_extensive_trace_all_terminal_vcg_conclusion
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
            model hvalue_nonneg hclick_mono model.click_pos rank hactive)
      terminal (fun rank => by rfl) hno_active

/--
Cold-start source-extensive all-terminal endpoint from an explicit finite
clock-disciplined source trace. This is the source-extensive counterpart of the
belief-explicit trace checker above.
-/
theorem theorem8_cold_start_clock_disciplined_strategy_trace_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (htrace :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyTrace
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminal (fun rank => by rfl)
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  simpa [terminalRecordSourceExtensiveGame, theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    theorem8_clock_disciplined_strategy_trace_source_extensive_trace_all_terminal_vcg_conclusion
      model htrace
      (by
        intro rank hactive
        simpa [theorem8BStarThresholdBid] using
          paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
            model hvalue_nonneg hclick_mono model.click_pos rank hactive)
      terminal (fun rank => by rfl) hno_active

/--
No-overshoot terminal-record audit.  In any annotated no-overshoot terminal
history, every inactive rank is recorded at exactly its finite `B*` threshold.
-/
theorem theorem8_no_overshoot_terminal_record_eq_threshold_of_inactive
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    {rank : ℕ}
    (hinactive : ¬ terminal.finalState.IsActive rank) :
    terminal.finalState.lastDropout rank =
      some
        (theorem8BStarThresholdBid
          terminal.localModel.value terminal.localModel.clickThroughRate
          (terminal.localModel.remaining + 1) (rank + 1)) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_final_record_eq_threshold
      terminal hinactive

/--
Theorem 8 source-extensive terminal-record finite-schedule endpoint.  From a
sorted no-duplicate finite `B*` dropout schedule, Lean builds the no-overshoot
terminal history and returns a unique PBE whose predicate includes source
sequential rationality, concrete history, terminality, and the completed-rank
paper formula.
-/
theorem theorem8_terminal_record_source_extensive_schedule_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
All-scheduled version of the source-extensive finite-schedule endpoint.  This
is the common paper-checking form when the completed finite ranks are exactly
the ranks listed in the verified dropout schedule.
-/
theorem theorem8_terminal_record_source_extensive_schedule_all_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let completedRanks := scheduledRanks.toFinset
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_schedule_completed_rank_conclusion
      model initialState scheduledRanks.toFinset scheduledRanks hsorted hnodup
      hinitial_active hunscheduled
      (by
        intro rank hrank
        simpa using hrank)
      hvalue_nonneg hvalue_mono

/--
Trace-refined source-extensive finite-schedule endpoint.  This is the
one-stop review form for the finite-schedule extended-form boundary: Lean
generates the no-overshoot terminal history from the schedule and returns the
unique PBE, the named finite `B*` strategy, the generated history, terminality,
and the completed-rank paper formula.
-/
theorem theorem8_terminal_record_source_extensive_schedule_trace_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
Clock-disciplined trace-refined finite-schedule source-extensive endpoint.
Compared with the certificate-only schedule endpoint above, this route exposes
the explicit clock-disciplined source trace generated by the schedule and uses
the schedule final-clock corollary to discharge completed-rank threshold
premises.
-/
theorem theorem8_clock_disciplined_schedule_source_extensive_trace_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hstate_no_overshoot :
      ∀ rank,
        initialState.IsActive rank →
          initialState.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hunscheduled_active_threshold :
      ∀ scheduledRank,
        scheduledRank ∈ scheduledRanks →
          ∀ otherRank,
            otherRank ∉ scheduledRanks →
              initialState.IsActive otherRank →
                paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    model scheduledRank ≤
                  theorem8BStarThresholdBid
                    model.value model.clickThroughRate (model.remaining + 1)
                    (otherRank + 1))
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let htrace :=
      theorem8_clock_sorted_schedule_to_clock_disciplined_trace
        model initialState scheduledRanks hsorted hnodup
        (fun rank _hrank => hinitial_active rank)
        hunscheduled_active_threshold
    let terminalProof :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
        model
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
          model initialState scheduledRanks hsorted hnodup
          (fun rank _hrank => hinitial_active rank))
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem)
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminalProof hinitial_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    theorem8_clock_disciplined_strategy_trace_source_extensive_trace_completed_threshold_conclusion
      model
      (theorem8_clock_sorted_schedule_to_clock_disciplined_trace
        model initialState scheduledRanks hsorted hnodup
        (fun rank _hrank => hinitial_active rank)
        hunscheduled_active_threshold)
      hstate_no_overshoot
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
        model
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
          model initialState scheduledRanks hsorted hnodup
          (fun rank _hrank => hinitial_active rank))
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem))
      hinitial_active completedRanks
      (theorem8_clock_sorted_schedule_completed_threshold_le_final_clock
        model initialState scheduledRanks completedRanks hsorted hsubset)
      hvalue_nonneg hvalue_mono model.current_le model.click_pos

/--
Clock-disciplined trace-refined finite-schedule source-extensive endpoint with
the unscheduled-threshold side condition derived from the final unscheduled
terminality bound.
-/
theorem theorem8_clock_disciplined_schedule_source_extensive_trace_completed_conclusion_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hstate_no_overshoot :
      ∀ rank,
        initialState.IsActive rank →
          initialState.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let htrace :=
      theorem8_clock_sorted_schedule_to_clock_disciplined_trace
        model initialState scheduledRanks hsorted hnodup
        (fun rank _hrank => hinitial_active rank)
        (theorem8_clock_sorted_schedule_unscheduled_threshold_of_final_clock_lt_unscheduled
          model initialState scheduledRanks hsorted hunscheduled)
    let terminalProof :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
        model
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
          model initialState scheduledRanks hsorted hnodup
          (fun rank _hrank => hinitial_active rank))
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem)
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminalProof hinitial_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_clock_disciplined_schedule_source_extensive_trace_completed_conclusion
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active hstate_no_overshoot
      (theorem8_clock_sorted_schedule_unscheduled_threshold_of_final_clock_lt_unscheduled
        model initialState scheduledRanks hsorted hunscheduled)
      hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
Clock-disciplined trace-refined finite-schedule source-extensive endpoint with
both source side conditions derived from the final unscheduled terminality
bound. The caller supplies the clock-sorted no-duplicate schedule, initial
activity, terminality, completed-rank membership, and ordered value facts.
-/
theorem theorem8_clock_disciplined_schedule_source_extensive_trace_completed_conclusion_of_final_clock_lt_unscheduled_derive_initial_no_overshoot
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let hstate_no_overshoot :=
      theorem8_clock_sorted_schedule_initial_no_overshoot_of_final_clock_lt_unscheduled
        model initialState scheduledRanks hsorted hunscheduled
    let htrace :=
      theorem8_clock_sorted_schedule_to_clock_disciplined_trace
        model initialState scheduledRanks hsorted hnodup
        (fun rank _hrank => hinitial_active rank)
        (theorem8_clock_sorted_schedule_unscheduled_threshold_of_final_clock_lt_unscheduled
          model initialState scheduledRanks hsorted hunscheduled)
    let terminalProof :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
        model
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
          model initialState scheduledRanks hsorted hnodup
          (fun rank _hrank => hinitial_active rank))
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem)
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace hstate_no_overshoot terminalProof hinitial_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_clock_disciplined_schedule_source_extensive_trace_completed_conclusion_of_final_clock_lt_unscheduled
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active
      (theorem8_clock_sorted_schedule_initial_no_overshoot_of_final_clock_lt_unscheduled
        model initialState scheduledRanks hsorted hunscheduled)
      hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
Cold-start clock-disciplined trace-refined finite-schedule source-extensive
endpoint. The paper cold-start state supplies initial activity and initial
no-overshoot; the schedule supplies the explicit clock-disciplined source
trace and the final-clock completed-rank threshold check.
-/
theorem theorem8_cold_start_clock_disciplined_schedule_source_extensive_trace_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hunscheduled_threshold :
      ∀ scheduledRank,
        scheduledRank ∈ scheduledRanks →
          ∀ otherRank,
            otherRank ∉ scheduledRanks →
              paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  model scheduledRank ≤
                theorem8BStarThresholdBid
                  model.value model.clickThroughRate (model.remaining + 1)
                  (otherRank + 1))
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model paper_theorem8_bstar_ranked_threshold_cold_start_state
            scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let initialState := paper_theorem8_bstar_ranked_threshold_cold_start_state
    let htrace :=
      theorem8_clock_sorted_schedule_to_clock_disciplined_trace
        model initialState scheduledRanks hsorted hnodup
        (fun rank _hrank => by rfl)
        (by
          intro scheduledRank hscheduled otherRank hother_not_mem _hactive
          exact
            hunscheduled_threshold scheduledRank hscheduled otherRank
              hother_not_mem)
    let terminalProof :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
        model
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
          model initialState scheduledRanks hsorted hnodup
          (fun rank _hrank => by rfl))
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem)
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          model hvalue_nonneg hclick_mono model.click_pos)
        terminalProof (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace] using
    theorem8_clock_disciplined_schedule_source_extensive_trace_completed_conclusion
      model paper_theorem8_bstar_ranked_threshold_cold_start_state
      completedRanks scheduledRanks hsorted hnodup
      (fun rank => by rfl)
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      (by
        intro scheduledRank hscheduled otherRank hother_not_mem _hactive
        exact
          hunscheduled_threshold scheduledRank hscheduled otherRank
            hother_not_mem)
      hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
Cold-start clock-disciplined trace-refined finite-schedule source-extensive
endpoint with the unscheduled-threshold side condition derived from the final
unscheduled terminality bound.
-/
theorem theorem8_cold_start_clock_disciplined_schedule_source_extensive_trace_completed_conclusion_of_final_clock_lt_unscheduled
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model paper_theorem8_bstar_ranked_threshold_cold_start_state.clockPrice
        scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model paper_theorem8_bstar_ranked_threshold_cold_start_state
            scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let initialState := paper_theorem8_bstar_ranked_threshold_cold_start_state
    let htrace :=
      theorem8_clock_sorted_schedule_to_clock_disciplined_trace
        model initialState scheduledRanks hsorted hnodup
        (fun rank _hrank => by rfl)
        (theorem8_clock_sorted_schedule_unscheduled_threshold_of_final_clock_lt_unscheduled
          model initialState scheduledRanks hsorted hunscheduled)
    let terminalProof :=
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_strategy_terminal_of_unscheduled_threshold_gt
        model
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_of_clock_sorted_nodup
          model initialState scheduledRanks hsorted hnodup
          (fun rank _hrank => by rfl))
        (by
          intro rank hnot_mem
          simpa [theorem8BStarThresholdBid] using
            hunscheduled rank hnot_mem)
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_trace
        model htrace
        (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
          model hvalue_nonneg hclick_mono model.click_pos)
        terminalProof (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_cold_start_clock_disciplined_schedule_source_extensive_trace_completed_conclusion
      model completedRanks scheduledRanks hsorted hnodup
      (by
        intro scheduledRank hscheduled otherRank hother_not_mem
        exact
          theorem8_clock_sorted_schedule_unscheduled_threshold_of_final_clock_lt_unscheduled
            model paper_theorem8_bstar_ranked_threshold_cold_start_state
            scheduledRanks hsorted hunscheduled scheduledRank hscheduled
            otherRank hother_not_mem (by rfl))
      hunscheduled hsubset hvalue_nonneg hvalue_mono hclick_mono

/--
Belief-explicit no-overshoot terminal-history endpoint with the paper-facing
terminal-clock premise. If each completed rank's finite `B*` threshold has
been reached by the terminal clock, Lean derives completed-rank inactivity and
the displayed completed-rank formula in the non-vacuous belief checker.
-/
theorem theorem8_no_overshoot_terminal_record_belief_source_extensive_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      terminal completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Trace-refined belief-explicit no-overshoot terminal-history endpoint with the
paper-facing terminal-clock premise. The unique PBE witness is the named finite
`B*` strategy, carries the generated source history and terminality proof in a
consistent belief, and satisfies the displayed completed-rank paper formula.
-/
theorem theorem8_no_overshoot_terminal_record_belief_source_extensive_trace_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        terminal.localModel.value terminal.localModel.clickThroughRate
        terminal.localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      terminal completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Trace-refined belief-explicit no-overshoot endpoint with direct completed-rank
inactivity.  This is the belief-carrying analogue of
`theorem8_no_overshoot_terminal_record_source_extensive_trace_completed_rank_conclusion`.
-/
theorem theorem8_no_overshoot_terminal_record_belief_source_extensive_trace_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        terminal.localModel.value terminal.localModel.clickThroughRate
        terminal.localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  dsimp [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid]
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game
      terminal
  let namedStrategy :=
    paper_theorem8_bstar_ranked_threshold_strategy
      terminal.localModel.value terminal.localModel.clickThroughRate
      terminal.localModel.remaining
  refine ⟨namedStrategy, ?_, ?_⟩
  · have hpbe : G.PerfectBayesianEquilibrium namedStrategy := by
      exact
        (paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_iff_named_strategy
          terminal namedStrategy).mpr rfl
    have htrace :=
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_history_terminal_exact_drop_history
        terminal hpbe
    refine ⟨hpbe, rfl, htrace.1, htrace.2.1, htrace.2.2, ?_⟩
    intro rank hrank
    exact
      paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_pbe_completed_rank_paper_conclusion_of_no_overshoot
        terminal completedRanks inactive_on_completed hvalue_nonneg
        hvalue_mono hclick_mono hclick_pos hpbe rank hrank
  · intro strategy hstrategy
    exact hstrategy.2.1

/--
Raw no-overshoot history to trace-refined belief-explicit source-extensive
completed-rank conclusion using direct final inactivity on the completed ranks.
This is the belief-carrying analogue of
`theorem8_no_overshoot_strategy_history_source_extensive_trace_completed_rank_conclusion`.
-/
theorem theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  dsimp
  exact
    theorem8_no_overshoot_terminal_record_belief_source_extensive_trace_completed_rank_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      completedRanks inactive_on_completed hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Raw no-overshoot history to trace-refined belief-explicit source-extensive
completed-rank conclusion using terminal-clock threshold checks.
-/
theorem theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_completed_threshold_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
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
          theorem8BStarThresholdBid
              model.value model.clickThroughRate
              (model.remaining + 1) (rank + 1) ≤
            finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Raw no-overshoot history to trace-refined all-terminal belief-explicit
source-extensive conclusion.  This is the non-vacuous-belief counterpart of
`theorem8_no_overshoot_strategy_history_source_extensive_trace_all_terminal_vcg_conclusion`.
-/
theorem theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
  dsimp
  exact
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_no_overshoot
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      hno_active

/--
Trace-refined belief-explicit clock-disciplined endpoint with direct
completed-rank inactivity.
-/
theorem theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model state finalState)
    (hstate_no_overshoot :
      ∀ rank,
        state.IsActive rank →
          state.clockPrice ≤
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < model.clickThroughRate i) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_no_overshoot_terminal_record_belief_source_extensive_trace_completed_rank_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal initially_active)
      completedRanks inactive_on_completed hvalue_nonneg hvalue_mono
      hclick_mono hclick_pos

/--
Cold-start belief-explicit clock-disciplined trace endpoint with direct
completed-rank inactivity.  It derives initial timing/activity from the
cold-start state and keeps the generated history and terminality proof in the
belief object.
-/
theorem theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdClockDisciplinedStrategyHistory
        model paper_theorem8_bstar_ranked_threshold_cold_start_state
        finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ finalState.IsActive rank)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i)
    (hclick_mono : ∀ i,
      model.clickThroughRate (i + 1) ≤ model.clickThroughRate i) :
    let hstate_no_overshoot :=
      paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history
        model hhist hstate_no_overshoot terminal (fun rank => by rfl)
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminalCert
    let G := terminalRecordBeliefSourceExtensiveGame terminalCert
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_no_overshoot_terminal_certificate_of_clock_disciplined_history] using
    theorem8_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_rank_conclusion
      model hhist
      (paper_theorem8_bstar_ranked_threshold_cold_start_initial_no_overshoot
        model hvalue_nonneg hclick_mono model.click_pos)
      terminal (fun rank => by rfl) completedRanks inactive_on_completed
      hvalue_nonneg hvalue_mono hclick_mono model.click_pos

/--
Belief-explicit source-extensive finite-schedule endpoint.  This is the same
completed-rank paper formula as the terminal-record source-extensive checker,
but the PBE belief now carries the generated source history and terminality.
-/
theorem theorem8_belief_source_extensive_schedule_completed_rank_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
All-scheduled version of the belief-explicit source-extensive finite-schedule
endpoint.
-/
theorem theorem8_belief_source_extensive_schedule_all_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let completedRanks := scheduledRanks.toFinset
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_belief_source_extensive_schedule_completed_rank_conclusion
      model initialState scheduledRanks.toFinset scheduledRanks hsorted hnodup
      hinitial_active hunscheduled
      (by
        intro rank hrank
        simpa using hrank)
      hvalue_nonneg hvalue_mono

/--
Trace-refined belief-explicit finite-schedule endpoint.  It returns the named
finite `B*` PBE, generated history, terminality, exact finite `B*` dropout
trace, and completed-rank paper formula in the non-vacuous belief checker.
-/
theorem theorem8_belief_source_extensive_schedule_trace_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (completedRanks : Finset ℕ) (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hsubset :
      ∀ rank, rank ∈ completedRanks → rank ∈ scheduledRanks)
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_belief_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_clock_sorted_nodup_unscheduled_threshold_gt
      model initialState completedRanks scheduledRanks hsorted hnodup
      hinitial_active hunscheduled hsubset hvalue_nonneg hvalue_mono

/--
All-scheduled trace-refined belief-explicit source-extensive endpoint.
-/
theorem theorem8_belief_source_extensive_schedule_trace_all_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let completedRanks := scheduledRanks.toFinset
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordBeliefSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordBeliefSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_belief_source_extensive_schedule_trace_completed_conclusion
      model initialState scheduledRanks.toFinset scheduledRanks hsorted hnodup
      hinitial_active hunscheduled
      (by
        intro rank hrank
        simpa using hrank)
      hvalue_nonneg hvalue_mono

/--
All-scheduled trace-refined source-extensive endpoint.  This is the easiest
finite-schedule trace form when the reviewer wants every scheduled rank checked
against the displayed paper formula.
-/
theorem theorem8_terminal_record_source_extensive_schedule_trace_all_completed_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ)
    (scheduledRanks : List ℕ)
    (hsorted :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_clock_sorted
        model initialState.clockPrice scheduledRanks)
    (hnodup : scheduledRanks.Nodup)
    (hinitial_active : ∀ rank, initialState.IsActive rank)
    (hunscheduled :
      ∀ rank,
        rank ∉ scheduledRanks →
          (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
            model initialState scheduledRanks).clockPrice <
            theorem8BStarThresholdBid
              model.value model.clickThroughRate (model.remaining + 1)
              (rank + 1))
    (hvalue_nonneg : ∀ i, 0 ≤ model.value i)
    (hvalue_mono : ∀ i, model.value (i + 1) ≤ model.value i) :
    let completedRanks := scheduledRanks.toFinset
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        model initialState scheduledRanks hsorted hnodup hinitial_active
        hunscheduled
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        model.value model.clickThroughRate model.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_schedule_trace_completed_conclusion
      model initialState scheduledRanks.toFinset scheduledRanks hsorted hnodup
      hinitial_active hunscheduled
      (by
        intro rank hrank
        simpa using hrank)
      hvalue_nonneg hvalue_mono

/--
Cold-start paper-checking form of the source-extensive terminal-record
endpoint.  The input schedule is threshold-sorted, and the unique PBE carries
the generated history and terminality obligations inside the PBE predicate.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_conclusion
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
            theorem8BStarThresholdBid
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
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_strict_ordered_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model completedRanks scheduledPrefix lastRank hthreshold_sorted hnodup
      hunscheduled_last hsubset

/--
All-scheduled cold-start version of the source-extensive terminal-record
endpoint.  The completed finite rank set is the schedule itself, so the caller
does not supply a separate completed-rank subset proof.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_all_completed_conclusion
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
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let completedRanks := (scheduledPrefix ++ [lastRank]).toFinset
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
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
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_conclusion
      model (scheduledPrefix ++ [lastRank]).toFinset scheduledPrefix lastRank
      hthreshold_sorted hnodup hunscheduled_last
      (by
        intro rank hrank
        rw [List.mem_toFinset] at hrank
        exact hrank)

/--
Trace-refined cold-start threshold-sorted source-extensive endpoint.  This is
the paper-native finite-schedule trace form: threshold-sorted cold-start
schedule data gives unique PBE, named finite `B*` strategy, generated history,
terminality, and completed-rank formulas in one conclusion.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_trace_completed_conclusion
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
            theorem8BStarThresholdBid
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
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_strict_ordered_cold_start_threshold_sorted_nodup_last_threshold_lt_unscheduled
      model completedRanks scheduledPrefix lastRank hthreshold_sorted hnodup
      hunscheduled_last hsubset

/--
All-scheduled cold-start trace endpoint.  This removes the completed-rank
subset proof when the checked finite ranks are exactly the threshold-sorted
schedule.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_trace_all_completed_conclusion
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
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let completedRanks := (scheduledPrefix ++ [lastRank]).toFinset
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
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
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_trace_completed_conclusion
      model (scheduledPrefix ++ [lastRank]).toFinset scheduledPrefix lastRank
      hthreshold_sorted hnodup hunscheduled_last
      (by
        intro rank hrank
        rw [List.mem_toFinset] at hrank
        exact hrank)

/--
Cold-start one-rank source-extensive endpoint.  For a singleton schedule, the
only schedule-specific paper premise is that every unscheduled rank's threshold
lies above the scheduled rank's terminal clock.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_singleton_all_completed_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (lastRank : ℕ)
    (hunscheduled_last :
      ∀ rank,
        rank ≠ lastRank →
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              lastRank <
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let completedRanks := ([lastRank] : List ℕ).toFinset
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        [lastRank]
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_singleton
          model lastRank)
        (by simp) (fun rank => by rfl)
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          [] lastRank
          (fun rank hrank => hunscheduled_last rank (by simpa using hrank)))
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_all_completed_conclusion
      model [] lastRank
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted_singleton
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        lastRank)
      (by simp)
      (fun rank hrank => hunscheduled_last rank (by simpa using hrank))

/--
Cold-start two-rank source-extensive endpoint.  The paper-specific schedule
premises reduce to adjacent threshold order, distinct scheduled ranks, and the
unscheduled-threshold comparison against the second scheduled rank.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_pair_all_completed_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hnext :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          rank ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          nextRank)
    (hne : rank ≠ nextRank)
    (hunscheduled_last :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model)
                nextRank <
              theorem8BStarThresholdBid
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).value
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).clickThroughRate
                ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).remaining + 1)
                (otherRank + 1)) :
    let completedRanks := ([rank, nextRank] : List ℕ).toFinset
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        [rank, nextRank]
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_pair
          model rank nextRank hnext)
        (by simpa using hne) (fun rank => by rfl)
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          [rank] nextRank
          (fun otherRank hmem => by
            have hnot : otherRank ≠ rank ∧ otherRank ≠ nextRank := by
              simpa using hmem
            exact hunscheduled_last otherRank hnot.1 hnot.2))
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ otherRank,
          otherRank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy otherRank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_all_completed_conclusion
      model [rank] nextRank
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted_pair
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        rank nextRank hnext)
      (by simpa using hne)
      (fun otherRank hmem => by
        have hnot : otherRank ≠ rank ∧ otherRank ≠ nextRank := by
          simpa using hmem
        exact hunscheduled_last otherRank hnot.1 hnot.2)

/--
Cold-start one-rank trace endpoint.  For a singleton schedule, the trace
package requires only the unscheduled-threshold comparison.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_singleton_trace_all_completed_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (lastRank : ℕ)
    (hunscheduled_last :
      ∀ rank,
        rank ≠ lastRank →
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              lastRank <
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let completedRanks := ([lastRank] : List ℕ).toFinset
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        [lastRank]
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_singleton
          model lastRank)
        (by simp) (fun rank => by rfl)
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          [] lastRank
          (fun rank hrank => hunscheduled_last rank (by simpa using hrank)))
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_trace_all_completed_conclusion
      model [] lastRank
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted_singleton
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        lastRank)
      (by simp)
      (fun rank hrank => hunscheduled_last rank (by simpa using hrank))

/--
Cold-start two-rank trace conclusion as a proposition.  The theorem below proves
this package from adjacent threshold order, distinct scheduled ranks, and the
unscheduled-threshold comparison against the second scheduled rank.
-/
def theorem8_cold_start_pair_trace_all_completed_conclusion_statement
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hnext :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          rank ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          nextRank)
    (hne : rank ≠ nextRank)
    (hunscheduled_last :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model)
                nextRank <
              theorem8BStarThresholdBid
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).value
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).clickThroughRate
                ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).remaining + 1)
                (otherRank + 1)) : Prop :=
    let completedRanks := ([rank, nextRank] : List ℕ).toFinset
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    let terminal :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_of_clock_sorted_nodup_unscheduled_threshold_gt
        localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
        [rank, nextRank]
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_cold_start_clock_sorted_pair
          model rank nextRank hnext)
        (by simpa using hne) (fun rank => by rfl)
        (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_unscheduled_threshold_gt_of_append_singleton
          localModel paper_theorem8_bstar_ranked_threshold_cold_start_state
          [rank] nextRank
          (fun otherRank hmem => by
            have hnot : otherRank ≠ rank ∧ otherRank ≠ nextRank := by
              simpa using hmem
            exact hunscheduled_last otherRank hnot.1 hnot.2))
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        localModel.value localModel.clickThroughRate localModel.remaining
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
                ∀ otherRank,
                  otherRank ∈ completedRanks →
                    completedRankPaperFormula ordinary G strategy otherRank

/--
Cold-start two-rank trace endpoint.  The trace package reduces to adjacent
threshold order, distinct scheduled ranks, and the unscheduled-threshold
comparison against the second scheduled rank.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_pair_trace_all_completed_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hnext :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          rank ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          nextRank)
    (hne : rank ≠ nextRank)
    (hunscheduled_last :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model)
                nextRank <
              theorem8BStarThresholdBid
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).value
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).clickThroughRate
                ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).remaining + 1)
                (otherRank + 1)) :
    theorem8_cold_start_pair_trace_all_completed_conclusion_statement
      model rank nextRank hnext hne hunscheduled_last := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid,
    theorem8_cold_start_pair_trace_all_completed_conclusion_statement] using
    theorem8_terminal_record_source_extensive_cold_start_threshold_sorted_trace_all_completed_conclusion
      model [rank] nextRank
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_threshold_sorted_pair
        (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
          model)
        rank nextRank hnext)
      (by simpa using hne)
      (fun otherRank hmem => by
        have hnot : otherRank ≠ rank ∧ otherRank ≠ nextRank := by
          simpa using hmem
        exact hunscheduled_last otherRank hnot.1 hnot.2)

/--
Unordered cold-start two-rank trace endpoint.  For two distinct displayed
ranks, a single max-threshold terminality premise is enough: Lean chooses the
threshold-sorted order and returns the corresponding trace-full completed-rank
source-extensive conclusion.
-/
theorem theorem8_terminal_record_source_extensive_cold_start_pair_or_swap_trace_all_completed_conclusion
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hne : rank ≠ nextRank)
    (hunscheduled_after_max :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            max
                (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                    model)
                  rank)
                (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                  (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                    model)
                  nextRank) <
              theorem8BStarThresholdBid
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).value
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).clickThroughRate
                ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).remaining + 1)
                (otherRank + 1)) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        model
    (∃ hnext :
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
            localModel rank ≤
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
            localModel nextRank,
        ∃ hunscheduled_last :
          ∀ otherRank,
            otherRank ≠ rank →
              otherRank ≠ nextRank →
                paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    localModel nextRank <
                  theorem8BStarThresholdBid localModel.value
                    localModel.clickThroughRate (localModel.remaining + 1)
                    (otherRank + 1),
        theorem8_cold_start_pair_trace_all_completed_conclusion_statement
          model rank nextRank hnext hne hunscheduled_last) ∨
      (∃ hnext :
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
            localModel nextRank ≤
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
            localModel rank,
        ∃ hunscheduled_last :
          ∀ otherRank,
            otherRank ≠ nextRank →
              otherRank ≠ rank →
                paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    localModel rank <
                  theorem8BStarThresholdBid localModel.value
                    localModel.clickThroughRate (localModel.remaining + 1)
                    (otherRank + 1),
        theorem8_cold_start_pair_trace_all_completed_conclusion_statement
          model nextRank rank hnext (Ne.symm hne) hunscheduled_last) := by
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      model
  rcases le_total
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
        localModel rank)
      (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
        localModel nextRank) with hle | hle
  · refine Or.inl ⟨hle, ?_, ?_⟩
    · intro otherRank hother_rank hother_next
      have hmax :
          max
              (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                localModel rank)
              (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                localModel nextRank) <
            theorem8BStarThresholdBid localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (otherRank + 1) := by
        simpa [localModel] using
          hunscheduled_after_max otherRank hother_rank hother_next
      simpa [localModel, max_eq_right hle] using hmax
    · exact
      theorem8_terminal_record_source_extensive_cold_start_pair_trace_all_completed_conclusion
        model rank nextRank hle hne
        (fun otherRank hother_rank hother_next => by
          have hmax :
              max
                  (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    localModel rank)
                  (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    localModel nextRank) <
                theorem8BStarThresholdBid localModel.value localModel.clickThroughRate
                  (localModel.remaining + 1) (otherRank + 1) := by
            simpa [localModel] using
              hunscheduled_after_max otherRank hother_rank hother_next
          simpa [localModel, max_eq_right hle] using hmax)
  · refine Or.inr ⟨hle, ?_, ?_⟩
    · intro otherRank hother_next hother_rank
      have hmax :
          max
              (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                localModel rank)
              (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                localModel nextRank) <
            theorem8BStarThresholdBid localModel.value localModel.clickThroughRate
              (localModel.remaining + 1) (otherRank + 1) := by
        simpa [localModel] using
          hunscheduled_after_max otherRank hother_rank hother_next
      simpa [localModel, max_eq_left hle] using hmax
    · exact
      theorem8_terminal_record_source_extensive_cold_start_pair_trace_all_completed_conclusion
        model nextRank rank hle (Ne.symm hne)
        (fun otherRank hother_next hother_rank => by
          have hmax :
              max
                  (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    localModel rank)
                  (paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                    localModel nextRank) <
                theorem8BStarThresholdBid localModel.value localModel.clickThroughRate
                  (localModel.remaining + 1) (otherRank + 1) := by
            simpa [localModel] using
              hunscheduled_after_max otherRank hother_rank hother_next
          simpa [localModel, max_eq_left hle] using hmax)

/--
Cold-start singleton terminal-record audit.  The generated final state records
the scheduled rank exactly at its finite `B*` threshold and leaves precisely
the unscheduled ranks active.
-/
theorem theorem8_cold_start_singleton_terminal_record_and_active_iff
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (lastRank : ℕ)
    (hunscheduled_last :
      ∀ rank,
        rank ≠ lastRank →
          paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model)
              lastRank <
            theorem8BStarThresholdBid
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).value
              (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).clickThroughRate
              ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                model).remaining + 1)
              (rank + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_behavior_certificate_of_cold_start_singleton_last_threshold_lt_unscheduled
        model lastRank hunscheduled_last
    cert.finalState.lastDropout lastRank =
        some
          (theorem8BStarThresholdBid
            cert.localModel.value cert.localModel.clickThroughRate
            (cert.localModel.remaining + 1) (lastRank + 1)) ∧
      ∀ rank, cert.finalState.IsActive rank ↔ rank ≠ lastRank := by
  refine ⟨?_, ?_⟩
  · simpa [theorem8BStarThresholdBid] using
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_singleton_final_state_terminal_record_eq_threshold
        model lastRank hunscheduled_last
  · intro rank
    exact
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_singleton_final_state_active_iff_ne
        model lastRank rank hunscheduled_last

/--
Cold-start pair terminal-record audit.  The generated final state records both
scheduled ranks at their finite `B*` thresholds and leaves exactly the ranks
outside the scheduled pair active.
-/
theorem theorem8_cold_start_pair_terminal_records_and_active_iff
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (rank nextRank : ℕ)
    (hnext :
      paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          rank ≤
        paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
            model)
          nextRank)
    (hne : rank ≠ nextRank)
    (hunscheduled_last :
      ∀ otherRank,
        otherRank ≠ rank →
          otherRank ≠ nextRank →
            paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_price
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model)
                nextRank <
              theorem8BStarThresholdBid
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).value
                (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).clickThroughRate
                ((paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
                  model).remaining + 1)
                (otherRank + 1)) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_behavior_certificate_of_cold_start_pair_last_threshold_lt_unscheduled
        model rank nextRank hnext hne hunscheduled_last
    cert.finalState.lastDropout rank =
        some
          (theorem8BStarThresholdBid
            cert.localModel.value cert.localModel.clickThroughRate
            (cert.localModel.remaining + 1) (rank + 1)) ∧
      cert.finalState.lastDropout nextRank =
          some
            (theorem8BStarThresholdBid
              cert.localModel.value cert.localModel.clickThroughRate
              (cert.localModel.remaining + 1) (nextRank + 1)) ∧
        ∀ otherRank,
          cert.finalState.IsActive otherRank ↔
            otherRank ≠ rank ∧ otherRank ≠ nextRank := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [theorem8BStarThresholdBid] using
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_pair_first_final_state_terminal_record_eq_threshold
        model rank nextRank hnext hne hunscheduled_last
  · simpa [theorem8BStarThresholdBid] using
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_pair_second_final_state_terminal_record_eq_threshold
        model rank nextRank hnext hne hunscheduled_last
  · intro otherRank
    exact
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_history_certificate_pair_final_state_active_iff_ne
        model rank nextRank otherRank hnext hne hunscheduled_last

/--
Any PBE accepted by the source-extensive checker contains the concrete
strategy history and terminality proof for the audited terminal state.
-/
theorem theorem8_source_extensive_pbe_has_history_and_terminal
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    (hpbe : (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium strategy) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        strategy terminal.initialState terminal.finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        strategy terminal.finalState := by
  exact
    ⟨paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_strategy_history
        terminal hpbe,
      paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_terminal
        terminal hpbe⟩

/--
Any PBE accepted by the source-extensive checker also has the exact finite
`B*` dropout-history certificate behind the terminal records.  This combines
the PBE trace facts with the no-overshoot history ledger.
-/
theorem theorem8_source_extensive_pbe_has_history_terminal_and_exact_drop_history
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    (hpbe : (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium strategy) :
    PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        strategy terminal.initialState terminal.finalState ∧
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        strategy terminal.finalState ∧
        PaperTheorem8BStarRankedThresholdExactDropHistory
          terminal.localModel terminal.initialState terminal.finalState := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_history_terminal_exact_drop_history
      terminal hpbe

/--
The source-extensive checker accepts exactly the named finite `B*`
ranked-threshold strategy as PBE.
-/
theorem theorem8_source_extensive_pbe_iff_named_strategy
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium
        strategy ↔
      strategy =
        paper_theorem8_bstar_ranked_threshold_strategy
          terminal.localModel.value terminal.localModel.clickThroughRate
          terminal.localModel.remaining := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_iff_named_strategy
      terminal strategy

/--
If the audited source-extensive terminal state has no active ranks left, every
accepted PBE has terminal-record outcome equal to the VCG target.
-/
theorem theorem8_source_extensive_pbe_outcome_eq_vcg_of_no_overshoot
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    (hpbe : (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium strategy) :
    (terminalRecordSourceExtensiveGame terminal).outcomeOf strategy =
      (terminalRecordSourceExtensiveGame terminal).vcgOutcome := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_outcome_eq_vcg_of_no_overshoot
      terminal hno_active hpbe

/--
All-terminal source-extensive no-overshoot endpoint: the unique accepted PBE
has terminal-record outcome equal to the VCG target.
-/
theorem theorem8_source_extensive_exists_unique_pbe_with_outcome_eq_vcg_of_no_overshoot
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_outcome_eq_vcg_of_no_overshoot
      terminal hno_active

/--
All-terminal source-extensive no-overshoot component check: every accepted PBE
matches the VCG outcome on slot and per-click payment for each rank.
-/
theorem theorem8_source_extensive_pbe_slot_payment_eq_vcg_of_no_overshoot
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    (hpbe : (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium strategy)
    (rank : ℕ) :
    let G := terminalRecordSourceExtensiveGame terminal
    (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
      (G.outcomeOf strategy).paymentPerClick rank =
        G.vcgOutcome.paymentPerClick rank := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_slot_payment_eq_vcg_of_no_overshoot
      terminal hno_active hpbe rank

/--
All-terminal source-extensive no-overshoot component endpoint: the unique
accepted PBE matches the VCG outcome on every rank's slot and per-click
payment.
-/
theorem theorem8_source_extensive_exists_unique_pbe_with_slot_payment_eq_vcg_of_no_overshoot
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
            (G.outcomeOf strategy).paymentPerClick rank =
              G.vcgOutcome.paymentPerClick rank := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_slot_payment_eq_vcg_of_no_overshoot
      terminal hno_active

/--
If the audited source-extensive terminal state has no active ranks left, every
accepted PBE gives every bidder the VCG utility.
-/
theorem theorem8_source_extensive_pbe_utility_eq_vcg_of_no_overshoot
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank)
    {strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ}
    (hpbe : (terminalRecordSourceExtensiveGame terminal).PerfectBayesianEquilibrium strategy)
    (bidder : ℕ) :
    ((terminalRecordSourceExtensiveGame terminal).outcomeOf strategy).utility
        (terminalRecordSourceExtensiveGame terminal).environment
        (terminalRecordSourceExtensiveGame terminal).values bidder =
      ((terminalRecordSourceExtensiveGame terminal).vcgOutcome).utility
        (terminalRecordSourceExtensiveGame terminal).environment
        (terminalRecordSourceExtensiveGame terminal).values bidder := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_pbe_utility_eq_vcg_of_no_overshoot
      terminal hno_active hpbe bidder

/--
All-terminal source-extensive no-overshoot payoff endpoint: the unique
accepted PBE gives every bidder the VCG utility.
-/
theorem theorem8_source_extensive_exists_unique_pbe_with_utility_eq_vcg_of_no_overshoot
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ bidder,
          (G.outcomeOf strategy).utility G.environment G.values bidder =
            G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_utility_eq_vcg_of_no_overshoot
      terminal hno_active

/--
All-terminal source-extensive no-overshoot full endpoint: the unique accepted
PBE has VCG outcome equality, rankwise VCG slot/payment components, and VCG
bidder utilities.
-/
theorem theorem8_source_extensive_exists_unique_pbe_with_all_terminal_vcg_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    let G := terminalRecordSourceExtensiveGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        G.outcomeOf strategy = G.vcgOutcome ∧
          (∀ rank,
            (G.outcomeOf strategy).slotOf rank = G.vcgOutcome.slotOf rank ∧
              (G.outcomeOf strategy).paymentPerClick rank =
                G.vcgOutcome.paymentPerClick rank) ∧
            ∀ bidder,
              (G.outcomeOf strategy).utility G.environment G.values bidder =
                G.vcgOutcome.utility G.environment G.values bidder := by
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_all_terminal_vcg_conclusion_of_no_overshoot
      terminal hno_active

/--
Trace-refined all-terminal source-extensive endpoint.  The unique accepted PBE
is the named finite `B*` strategy, carries the generated history, terminality,
and exact finite `B*` dropout trace, and has the full VCG outcome,
slot/payment, and utility conclusion.
-/
theorem theorem8_source_extensive_trace_all_terminal_vcg_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        terminal.localModel.value terminal.localModel.clickThroughRate
        terminal.localModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
              strategy terminal.initialState terminal.finalState ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                strategy terminal.finalState ∧
              PaperTheorem8BStarRankedThresholdExactDropHistory
                  terminal.localModel terminal.initialState terminal.finalState ∧
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
  simpa [terminalRecordSourceExtensiveGame] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_all_terminal_vcg_conclusion_of_no_overshoot
      terminal hno_active

/--
Raw no-overshoot history to trace-refined all-terminal source-extensive
conclusion. This is the one-stop all-rank route from a concrete no-overshoot
source history, terminality, initial activity, and all-ranks terminal
inactivity.
-/
theorem theorem8_no_overshoot_strategy_history_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8BStarRankedThresholdNoOvershootStrategyHistory
        model state finalState)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  dsimp
  exact
    theorem8_source_extensive_trace_all_terminal_vcg_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history
        model hhist terminal initially_active)
      hno_active

/--
One-stop all-terminal source-extensive endpoint from an ordinary generated
named-strategy history plus the realized-new-dropout no-overshoot invariant.
This is the closest current interface to the remaining concrete source proof:
it consumes the source-extensive generated history, terminality, initial
activity, all-terminality, and the step-local timing invariant, then returns
unique PBE, named-strategy identity, generated-history/terminal/exact-record
trace, and VCG outcome/slot-payment/utility conclusions.
-/
theorem theorem8_strategy_history_realized_new_dropout_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      ∀ {state next : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
        {rank : ℕ},
        PaperTheorem8GeneralizedEnglishAuctionState.StrategyStep
          (paper_theorem8_bstar_ranked_threshold_strategy
            model.value model.clickThroughRate model.remaining) state next →
        state.IsActive rank →
        ¬ next.IsActive rank →
        state.clockPrice ≤
          theorem8BStarThresholdBid
            model.value model.clickThroughRate (model.remaining + 1)
            (rank + 1))
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout
        model hhist hno_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  dsimp
  exact
    theorem8_source_extensive_trace_all_terminal_vcg_conclusion
      (theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout
        model hhist hno_overshoot terminal initially_active)
      hno_active

/--
Named-source-timing form of the one-stop all-terminal source-extensive
endpoint. This is the stable target for a future concrete source proof: prove
`theorem8RealizedNewDropoutNoOvershootStatement model`, generated history,
terminality, initial activity, and all-terminality, then Lean returns unique
PBE, named-strategy identity, generated/exact trace, and VCG conclusions.
-/
theorem theorem8_strategy_history_realized_new_dropout_statement_source_extensive_trace_all_terminal_vcg_conclusion
    (model : PaperTheorem8BStarRankedThresholdLocalOptimalityCertificate)
    {state finalState : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    (hhist :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        state finalState)
    (hno_overshoot :
      theorem8RealizedNewDropoutNoOvershootStatement model)
    (terminal :
      PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
        (paper_theorem8_bstar_ranked_threshold_strategy
          model.value model.clickThroughRate model.remaining)
        finalState)
    (initially_active : ∀ rank, state.IsActive rank)
    (hno_active : ∀ rank, ¬ finalState.IsActive rank) :
    let terminalCert :=
      theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout_statement
        model hhist hno_overshoot terminal initially_active
    let G := terminalRecordSourceExtensiveGame terminalCert
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
  dsimp
  exact
    theorem8_strategy_history_realized_new_dropout_source_extensive_trace_all_terminal_vcg_conclusion
      model hhist hno_overshoot terminal initially_active hno_active

/--
One-stop source-extensive no-overshoot paper-checking endpoint.  The unique
PBE witness is the named finite `B*` strategy, carries the concrete generated
history and terminality proof, and satisfies the displayed completed-rank
paper formula whenever the terminal clock has reached that rank's finite `B*`
threshold.
-/
theorem theorem8_no_overshoot_terminal_record_source_extensive_trace_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceExtensiveGame terminal
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        terminal.localModel.value terminal.localModel.clickThroughRate
        terminal.localModel.remaining
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
                    completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceExtensiveGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_exists_unique_pbe_with_trace_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      terminal completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Theorem 8 source-shaped terminal-record endpoint for finite paper checks.  If
the exact terminal records have reached each completed rank's finite `B*`
threshold, Lean derives unique PBE and the displayed completed-rank formula.
-/
theorem theorem8_terminal_record_source_completed_rank_conclusion
    (terminal : PaperTheorem8BStarRankedThresholdTerminalHistoryBehaviorCertificate)
    (exact_history :
      PaperTheorem8BStarRankedThresholdExactDropHistory
        terminal.localModel terminal.initialState terminal.finalState)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let G := terminalRecordSourceGame terminal
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula terminal G strategy rank := by
  simpa [terminalRecordSourceGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_exact_history_completed_threshold_le
      terminal exact_history completedRanks hcompleted_threshold_le
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
Theorem 8 no-overshoot version of the source-shaped terminal-record endpoint.
This is the finite-history route most aligned with the paper's dropout
history proof: threshold-reached premises imply the completed-rank formulas.
-/
theorem theorem8_no_overshoot_terminal_record_source_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    (hvalue_nonneg : ∀ i, 0 ≤ terminal.localModel.value i)
    (hvalue_mono : ∀ i,
      terminal.localModel.value (i + 1) ≤ terminal.localModel.value i)
    (hclick_mono : ∀ i,
      terminal.localModel.clickThroughRate (i + 1) ≤
        terminal.localModel.clickThroughRate i)
    (hclick_pos : ∀ i, 0 < terminal.localModel.clickThroughRate i) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let G := terminalRecordSourceGame ordinary
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      G.PerfectBayesianEquilibrium strategy ∧
        ∀ rank,
          rank ∈ completedRanks →
            completedRankPaperFormula ordinary G strategy rank := by
  simpa [terminalRecordSourceGame, completedRankPaperFormula,
    theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_sequential_dynamic_game_exists_unique_pbe_with_completed_rank_paper_conclusion_of_no_overshoot_completed_threshold_le
      terminal completedRanks hcompleted_threshold_le
      hvalue_nonneg hvalue_mono hclick_mono hclick_pos

/--
No-overshoot terminal-history ex-post local-deviation source-completion
endpoint.  The annotated no-overshoot history supplies exact finite `B*`
records, and the terminal-clock premise supplies completed-rank inactivity, so
the local-deviation checker yields unique PBE with terminal-record formulas for
the completed ranks.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_source_completion_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_history_ex_post_local_deviation_source_completion_certificate_of_completed_threshold_le
        terminal model hmodel completedRanks
        (by
          intro rank hrank
          simpa [theorem8BStarThresholdBid] using
            hcompleted_threshold_le rank hrank)
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.source.integrated.dynamic.base.game.PerfectBayesianEquilibrium
          strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          cert.source.integrated strategy ∧
          ∀ rank,
            rank ∈ cert.completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.source.integrated.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.source.integrated.terminal.finalState).paymentPerClick
                    rank =
                  theorem8BStarThresholdBid
                    cert.source.integrated.terminal.localModel.value
                    cert.source.integrated.terminal.localModel.clickThroughRate
                    (cert.source.integrated.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.source.integrated.terminal.localModel.clickThroughRate
                      rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.source.integrated.terminal.localModel.value
                      cert.source.integrated.terminal.localModel.clickThroughRate
                      rank
                      (cert.source.integrated.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank ≤
                        cert.source.integrated.terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le
      terminal model hmodel completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
No-overshoot terminal-history ex-post source-completion endpoint with completed
ranks supplied directly as inactive terminal ranks. This avoids restating a
terminal-clock threshold inequality when the completed set is already certified
from the history.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_source_completion_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_history_ex_post_local_deviation_source_completion_certificate_of_local_deviation
        terminal model hmodel completedRanks inactive_on_completed
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.source.integrated.dynamic.base.game.PerfectBayesianEquilibrium
          strategy ∧
        PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicPBEConclusion
          cert.source.integrated strategy ∧
          ∀ rank,
            rank ∈ cert.completedRanks →
              (paper_theorem8_terminal_dropout_record_outcome
                cert.source.integrated.terminal.finalState).slotOf rank =
                  some rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  cert.source.integrated.terminal.finalState).paymentPerClick
                    rank =
                  theorem8BStarThresholdBid
                    cert.source.integrated.terminal.localModel.value
                    cert.source.integrated.terminal.localModel.clickThroughRate
                    (cert.source.integrated.terminal.localModel.remaining + 1)
                    (rank + 1) ∧
                  cert.source.integrated.terminal.localModel.clickThroughRate
                      rank *
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank =
                    paper_theorem7_ranked_vcg_tail_payment
                      cert.source.integrated.terminal.localModel.value
                      cert.source.integrated.terminal.localModel.clickThroughRate
                      rank
                      (cert.source.integrated.terminal.localModel.remaining + 1) ∧
                    0 ≤
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank ∧
                      (paper_theorem8_terminal_dropout_record_outcome
                        cert.source.integrated.terminal.finalState).paymentPerClick
                        rank ≤
                        cert.source.integrated.terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_history_ex_post_local_deviation_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_local_deviation
      terminal model hmodel completedRanks inactive_on_completed

/--
Trace-full no-overshoot ex-post source-completion endpoint.  This is the
local-deviation checker version to use when the human review should see the
PBE uniqueness, named finite `B*` strategy, generated history, terminality,
exact dropout trace, and completed-rank formulas in one statement.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_trace_full_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_no_overshoot_terminal_dynamic_certificate
        terminal model hmodel
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_dynamic_certificate_to_terminal_dynamic_certificate
        cert
    let namedStrategy :=
      paper_theorem8_bstar_ranked_threshold_strategy
        cert.dynamic.base.strictModel.value
        cert.dynamic.base.strictModel.clickThroughRate
        cert.dynamic.base.strictModel.remaining
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        strategy = namedStrategy ∧
          PaperTheorem8BStarRankedThresholdStrictOrderedTerminalDynamicFullPBEConclusion
              ordinary strategy ∧
            PaperTheorem8GeneralizedEnglishAuctionState.StrategyHistory
                strategy cert.terminal.initialState cert.terminal.finalState ∧
              PaperTheorem8GeneralizedEnglishAuctionState.StrategyTerminal
                  strategy cert.terminal.finalState ∧
                PaperTheorem8BStarRankedThresholdExactDropHistory
                    cert.terminal.localModel cert.terminal.initialState
                    cert.terminal.finalState ∧
                  ∀ rank,
                    rank ∈ completedRanks →
                      completedRankTerminalRecordFormula cert.terminal rank := by
  simpa [theorem8BStarThresholdBid, completedRankTerminalRecordFormula] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_no_overshoot_terminal_dynamic_exists_unique_pbe_with_trace_full_completed_rank_terminal_record_conclusion_of_completed_threshold_le
      terminal model hmodel completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Payoff-facing form of the no-overshoot ex-post source-completion route: every
completed rank has the same utility in the terminal dropout-record outcome and
the constructed successor-tail finite `B*` outcome.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_source_completion_utility_eq_bstar_of_completed_threshold
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    (paper_theorem8_terminal_dropout_record_outcome
        terminal.finalState).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        terminal.localModel.value terminal.localModel.clickThroughRate
        (terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_completed_threshold_le
      terminal model hmodel completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hrank

/--
Payoff-facing no-overshoot ex-post source-completion route with completed
ranks supplied directly as inactive terminal ranks.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_source_completion_utility_eq_bstar_of_completed_rank
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    (paper_theorem8_terminal_dropout_record_outcome
        terminal.finalState).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        terminal.localModel.value terminal.localModel.clickThroughRate
        (terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank := by
  exact
    paper_theorem8_bstar_ranked_threshold_strict_ordered_no_overshoot_terminal_history_ex_post_local_deviation_source_completion_terminal_record_utility_eq_bstar_of_local_deviation
      terminal model hmodel completedRanks inactive_on_completed hrank

/--
Source-sequential no-overshoot terminal-history source-completion endpoint.
This version uses the compact source-shaped dynamic checker, so the
source-sequential rationality iff and belief consistency are supplied by the
constructed game rather than as external review obligations.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_source_completion_completed_threshold_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model terminal.initialState).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model hmodel
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
                  theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_completed_threshold_le
      terminal model hmodel completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)

/--
Source-sequential no-overshoot terminal-history source-completion endpoint with
completed ranks supplied directly as inactive terminal ranks. This avoids
duplicating the history-derived completed-rank fact as a terminal-clock
threshold inequality.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_source_completion_completed_rank_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model terminal.initialState).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank) :
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_dynamic_certificate
        terminal model hmodel
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
                  theorem8BStarThresholdBid
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
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_source_completion_exists_unique_pbe_with_terminal_record_conclusion_of_inactive_completed
      terminal model hmodel completedRanks inactive_on_completed

/--
Payoff-facing form of the source-sequential no-overshoot terminal-history
route: completed ranks have the same utility in terminal dropout records and
the constructed successor-tail finite `B*` outcome.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_source_completion_utility_eq_bstar_of_completed_threshold
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model terminal.initialState).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (hcompleted_threshold_le :
      ∀ rank,
        rank ∈ completedRanks →
          theorem8BStarThresholdBid
              terminal.localModel.value terminal.localModel.clickThroughRate
              (terminal.localModel.remaining + 1) (rank + 1) ≤
            terminal.finalState.clockPrice)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    (paper_theorem8_terminal_dropout_record_outcome
        terminal.finalState).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        terminal.localModel.value terminal.localModel.clickThroughRate
        (terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_source_completion_terminal_record_utility_eq_bstar_of_completed_threshold_le
      terminal model hmodel completedRanks
      (by
        intro rank hrank
        simpa [theorem8BStarThresholdBid] using
          hcompleted_threshold_le rank hrank)
      hrank

/--
Payoff-facing source-sequential no-overshoot terminal-history endpoint from
direct completed-rank inactivity.
-/
theorem theorem8_source_sequential_no_overshoot_terminal_history_source_completion_utility_eq_bstar_of_completed_rank
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_constructed_outcome_certificate
            model terminal.initialState).base.strictModel =
        terminal.localModel)
    (completedRanks : Finset ℕ)
    (inactive_on_completed :
      ∀ rank, rank ∈ completedRanks → ¬ terminal.finalState.IsActive rank)
    {rank : ℕ} (hrank : rank ∈ completedRanks) :
    (paper_theorem8_terminal_dropout_record_outcome
        terminal.finalState).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank =
      (paper_theorem8_bstar_ranked_threshold_outcome
        terminal.localModel.value terminal.localModel.clickThroughRate
        (terminal.localModel.remaining + 1)).utility
        ({ clickThroughRate := terminal.localModel.clickThroughRate } :
          PositionEnvironment ℕ)
        terminal.localModel.value rank := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_source_sequential_no_overshoot_terminal_history_source_completion_terminal_record_utility_eq_bstar_of_inactive_completed
      terminal model hmodel completedRanks inactive_on_completed hrank

/--
Behavioral checkpoint for the no-overshoot ex-post source-completion route:
the concrete local-deviation checker accepts exactly the named finite `B*`
ranked-threshold strategy as PBE.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_source_completion_pbe_iff_named_strategy
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ) :
    let ordinary :=
      paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal
    let cert :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_certificate
        ordinary model hmodel
    cert.dynamic.base.game.PerfectBayesianEquilibrium strategy ↔
      strategy =
        paper_theorem8_bstar_ranked_threshold_strategy
          cert.dynamic.base.strictModel.value
          cert.dynamic.base.strictModel.clickThroughRate
          cert.dynamic.base.strictModel.remaining := by
  simpa using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_pbe_iff_named_strategy
      (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
        terminal)
      model hmodel (strategy := strategy)

/--
All-rank no-overshoot terminal-history ex-post source-completion endpoint.
When the annotated terminal history has no active ranks left, the concrete
local-deviation checker gives a unique PBE and the ordered terminal-record
paper conclusion for every rank: assigned rank, finite `B*` payment, VCG-tail
accounting, payment interval, individual rationality, and no positive
transfers.
-/
theorem theorem8_ex_post_no_overshoot_terminal_history_source_completion_ordered_terminal_record_conclusion
    (terminal :
      PaperTheorem8BStarRankedThresholdNoOvershootTerminalHistoryBehaviorCertificate)
    (model :
      PaperTheorem8BStarRankedThresholdStrictOrderedLocalOptimalityCertificate)
    (hmodel :
      paper_theorem8_bstar_ranked_threshold_local_optimality_certificate_of_strict
          (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_constructed_outcome_certificate
            model).base.strictModel =
        terminal.localModel)
    (hno_active : ∀ rank, ¬ terminal.finalState.IsActive rank) :
    ∃! strategy : PaperTheorem8GeneralizedEnglishStrategy ℕ,
      (paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_terminal_dynamic_certificate
        (paper_theorem8_bstar_ranked_threshold_no_overshoot_terminal_history_behavior_certificate_to_terminal_history_behavior_certificate
          terminal)
        model hmodel).dynamic.base.game.PerfectBayesianEquilibrium strategy ∧
        (∀ rank,
          (paper_theorem8_terminal_dropout_record_outcome
            terminal.finalState).slotOf rank =
            some rank) ∧
          (∀ rank,
            (paper_theorem8_terminal_dropout_record_outcome
              terminal.finalState).paymentPerClick rank =
              theorem8BStarThresholdBid
                terminal.localModel.value terminal.localModel.clickThroughRate
                (terminal.localModel.remaining + 1) (rank + 1)) ∧
            (∀ rank,
              terminal.localModel.clickThroughRate rank *
                  (paper_theorem8_terminal_dropout_record_outcome
                    terminal.finalState).paymentPerClick rank =
                paper_theorem7_ranked_vcg_tail_payment
                  terminal.localModel.value terminal.localModel.clickThroughRate
                  rank (terminal.localModel.remaining + 1)) ∧
              (∀ rank,
                0 ≤
                  (paper_theorem8_terminal_dropout_record_outcome
                    terminal.finalState).paymentPerClick rank ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  terminal.finalState).paymentPerClick rank ≤
                  terminal.localModel.value rank) ∧
                (paper_theorem8_terminal_dropout_record_outcome
                  terminal.finalState).IndividuallyRational
                  ({ clickThroughRate := terminal.localModel.clickThroughRate } :
                    PositionEnvironment ℕ)
                  terminal.localModel.value ∧
                  paper_position_no_positive_transfers
                    (paper_theorem8_terminal_dropout_record_outcome
                      terminal.finalState) := by
  simpa [theorem8BStarThresholdBid] using
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_ex_post_local_deviation_core_source_completion_exists_unique_pbe_with_ordered_terminal_record_paper_conclusion_of_no_overshoot_terminal_history
      terminal model hmodel hno_active

end

end PaperInterface
end EOS07GSP
