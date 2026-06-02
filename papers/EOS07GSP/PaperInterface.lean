import EOS07GSP.ProofInterface
import EOS07GSP.PostPaperAudit

/-!
# Paper Interface: Internet Advertising and the Generalized Second-Price Auction

This is the compact human-review surface for Edelman, Ostrovsky, and Schwarz,
*Internet Advertising and the Generalized Second-Price Auction*.  It exposes the
paper-facing definitions and named results; implementation and audit ledgers
remain in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

namespace EOS07GSP
namespace PaperInterface

/-- Definition 4: locally envy-free outcome predicate. -/
abbrev definition4_locally_envy_free := @locallyEnvyFree

/-- Stable-assignment predicate used by the paper's stable-assignment bridge. -/
abbrev stable_assignment := @stableAssignment

/-- Remark 1: truthful GSP payments weakly dominate VCG per-click payments. -/
abbrev remark1_gsp_payments_weakly_dominate_vcg :=
  @EOS07GSP.audit_remark1_truthful_gsp_payment_weakly_dominates_vcg_per_click

/-- Remark 2: VCG position mechanism is truthful. -/
abbrev remark2_vcg_truthful :=
  @EOS07GSP.audit_remark2_vcg_position_mechanism_truthful

/-- Remark 3: GSP is not dominant-strategy truthful. -/
abbrev remark3_gsp_not_truthful :=
  @EOS07GSP.audit_gsp_not_dominant_strategy_truthful

/-- Running example: truthful GSP bids are a Nash equilibrium. -/
abbrev running_example_truthful_gsp_nash :=
  @EOS07GSP.audit_running_example_truthful_gsp_is_nash

/-- Running example: truthful GSP revenue exceeds VCG revenue. -/
abbrev running_example_truthful_gsp_revenue_comparison :=
  @EOS07GSP.audit_running_example_truthful_gsp_revenue_gt_vcg_revenue

/-- Lemma 5: locally envy-free equilibrium gives a stable assignment. -/
abbrev lemma5_locally_envy_free_stable :=
  @EOS07GSP.audit_lemma5_locally_envy_free_equilibrium_stable_assignment

/-- Lemma 6: stable assignment gives a locally envy-free outcome. -/
abbrev lemma6_stable_assignment_slot_envy_free :=
  @EOS07GSP.audit_lemma6_stable_assignment_slot_envy_free

/-- Theorem 7: ranked `B*` payment identity. -/
abbrev theorem7_bstar_payment_identity :=
  @EOS07GSP.audit_theorem7_bstar_payment_identity

/-- Theorem 7: canonical tail conclusion with no positive transfers. -/
abbrev theorem7_no_positive_transfer_conclusion :=
  @EOS07GSP.audit_theorem7_ordered_ranked_canonical_tail_no_positive_transfer_paper_conclusion

/-- Theorem 8: dropout price equals the `B*` bid. -/
abbrev theorem8_dropout_price_bstar :=
  @EOS07GSP.audit_theorem8_ranked_dropout_price_eq_bstar_bid_of_vcg_tail

/-- Theorem 8: no-overshoot dropout steps record exactly the finite `B*` bid. -/
abbrev theorem8_no_overshoot_dropout_step_exact_record :=
  @EOS07GSP.audit_theorem8_bstar_ranked_threshold_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot

/-- Theorem 8: exact dropout records are equivalent to realized no overshoot. -/
abbrev theorem8_dropout_step_no_overshoot_iff_exact_record :=
  @EOS07GSP.audit_theorem8_strategy_step_new_dropout_no_overshoot_iff_record_eq_threshold

/-- Theorem 8: named source-timing bridge for realized dropout no-overshoot. -/
abbrev theorem8_realized_dropout_no_overshoot_source_timing_bridge :=
  @EOS07GSP.audit_theorem8_bstar_ranked_threshold_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot_statement

/-- Theorem 8: source-extensive PBE iff named strategy. -/
abbrev theorem8_source_extensive_pbe_iff_named_strategy_review :=
  @EOS07GSP.PaperInterface.theorem8_source_extensive_pbe_iff_named_strategy

/-- Theorem 8: source-extensive PBE has the VCG outcome under no overshoot. -/
abbrev theorem8_source_extensive_outcome_eq_vcg :=
  @theorem8_source_extensive_pbe_outcome_eq_vcg_of_no_overshoot

/-- Theorem 8: local-advance-safe histories satisfy finite `B*` formulas. -/
abbrev theorem8_local_advance_safe_completed_rank_source_extensive :=
  @EOS07GSP.audit_theorem8_strategy_history_local_advance_safe_trace_completed_threshold_conclusion

/-- Theorem 8: cold-start local-advance-safe histories satisfy finite `B*` formulas. -/
abbrev theorem8_cold_start_local_advance_safe_completed_rank_source_extensive :=
  @EOS07GSP.audit_theorem8_cold_start_strategy_history_local_advance_safe_trace_completed_threshold_conclusion

/-- Theorem 8: local-deviation terminal records satisfy finite `B*` formulas. -/
abbrev theorem8_local_deviation_terminal_record_completed_schedule :=
  @EOS07GSP.audit_theorem8_terminal_record_local_deviation_cold_start_threshold_sorted_all_completed_conclusion

/-- Theorem 8: local-deviation terminal-dynamic full PBE conclusion. -/
abbrev theorem8_local_deviation_terminal_dynamic_full_conclusion :=
  @EOS07GSP.audit_theorem8_local_deviation_cold_start_threshold_sorted_terminal_dynamic_full_conclusion

/-- Theorem 8: exact-record source game full VCG conclusion. -/
abbrev theorem8_exact_record_full_vcg_conclusion :=
  @theorem8_finite_active_exact_record_source_game_full_vcg_conclusion

/-- Theorem 8: complete finite source schedule gives the displayed PBE formulas. -/
abbrev theorem8_complete_finite_schedule_source_extensive_displayed_conclusion :=
  @EOS07GSP.audit_theorem8_strict_ordered_complete_fin_schedule_source_extensive_trace_full_displayed_conclusion_of_threshold_sorted

/-- Theorem 8: price-sorted finite schedule discharges source-event obligations. -/
abbrev theorem8_price_sorted_finite_schedule_source_event_boundary :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_source_event_boundary

/-- Theorem 8: price-sorted finite source event gives full VCG conclusion. -/
abbrev theorem8_price_sorted_finite_schedule_source_event_threshold_event_vcg :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_source_event_threshold_event_trace_full_vcg_conclusion

/-- Theorem 8: belief price-sorted finite source event gives full VCG conclusion. -/
abbrev theorem8_price_sorted_finite_schedule_belief_source_event_threshold_event_vcg :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_belief_source_event_threshold_event_trace_full_vcg_conclusion

/-- Theorem 8: price-sorted finite schedule gives ordered displayed PBE formulas. -/
abbrev theorem8_price_sorted_finite_schedule_source_event_ordered_displayed_conclusion :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_source_event_trace_ordered_displayed_paper_conclusion

/-- Theorem 8: belief-explicit price-sorted finite schedule conclusion. -/
abbrev theorem8_price_sorted_finite_schedule_belief_source_event_ordered_displayed_conclusion :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_belief_source_event_trace_ordered_displayed_paper_conclusion

/-- Theorem 8: price-sorted finite source-event boundary plus ordered payoff. -/
abbrev theorem8_price_sorted_finite_schedule_source_event_boundary_ordered_displayed_conclusion :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_source_event_boundary_ordered_displayed_paper_conclusion

/-- Theorem 8: belief price-sorted source-event boundary plus ordered payoff. -/
abbrev theorem8_price_sorted_finite_schedule_belief_source_event_boundary_ordered_displayed_conclusion :=
  @EOS07GSP.audit_theorem8_strict_ordered_price_sorted_fin_schedule_belief_source_event_boundary_ordered_displayed_paper_conclusion

end PaperInterface
end EOS07GSP
