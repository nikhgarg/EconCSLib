import EconCSLean.Online.AdWords

/-!
# Paper-Facing Theorems: AdWords and Generalized Online Matching

This file is the public theorem interface for the Mehta-Saberi-Vazirani-Vazirani
AdWords formalization. Detailed finite assignment, Balance/MSVV choice, and
LP-duality lemmas live in `AdWords.lean`.
-/

namespace EconCSLean
namespace Online

/--
The empty AdWords assignment is budget-feasible when budgets are nonnegative.
-/
theorem paper_adwords_empty_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.Feasible (AdWordsInstance.emptyAssignment :
      AdWordsInstance.Assignment Advertiser Query) := by
  exact AdWordsInstance.emptyAssignment_feasible I hbudget

set_option linter.unusedFintypeInType false in
/--
Finite AdWords instances have an offline optimum assignment.
-/
theorem paper_adwords_offline_optimum_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    ∃ A : AdWordsInstance.Assignment Advertiser Query,
      I.IsOptimalAssignment A := by
  exact AdWordsInstance.exists_optimalAssignment I hbudget

/--
Every feasible AdWords assignment earns at most total advertiser budget.
-/
theorem paper_adwords_revenue_le_total_budget_of_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.revenue A ≤ ∑ a : Advertiser, I.budget a := by
  exact AdWordsInstance.revenue_le_totalBudget_of_feasible I A hfeasible

/--
Weak duality for the standard finite AdWords LP: any nonnegative dual variables
covering each bid upper-bound the revenue of every feasible assignment.
-/
theorem paper_adwords_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.Feasible A)
    (hdual : I.DualFeasible alpha beta) :
    I.revenue A ≤ I.dualObjective alpha beta := by
  exact AdWordsInstance.revenue_le_dualObjective_of_dualFeasible
    I A alpha beta hfeasible hdual

/--
Integral AdWords assignments embed as feasible `0/1` fractional LP solutions.
-/
theorem paper_adwords_integral_assignment_fractional_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.FractionalFeasible (AdWordsInstance.assignmentFraction A) := by
  exact AdWordsInstance.assignmentFraction_fractionalFeasible_of_feasible
    I A hfeasible

/--
Fractional weak duality for the standard AdWords LP.
-/
theorem paper_adwords_fractional_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : AdWordsInstance.FractionalAssignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible X)
    (hdual : I.DualFeasible alpha beta) :
    I.fractionalRevenue X ≤ I.dualObjective alpha beta := by
  exact AdWordsInstance.fractionalRevenue_le_dualObjective_of_dualFeasible
    I X alpha beta hfeasible hdual

/--
Dual-feasibility builder in the form used by the Balance/MSVV analysis: it is
enough to lower-bound every query dual `beta q` by the advertiser slack score
`bid a q * (1 - alpha a)`.
-/
theorem paper_adwords_dual_feasible_of_slack_score_bound
    {Advertiser Query : Type*}
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a)
    (hbeta : ∀ q, 0 ≤ beta q)
    (hcover : ∀ a q, I.slackScore alpha a q ≤ beta q) :
    I.DualFeasible alpha beta := by
  exact AdWordsInstance.dualFeasible_of_slackScore_le_beta
    I alpha beta halpha hbeta hcover

/--
Finite max-slack construction of query duals: for any nonnegative advertiser
dual `alpha`, setting each `beta q` to the nonnegative maximum slack score over
advertisers gives a dual-feasible AdWords LP solution.
-/
theorem paper_adwords_dual_feasible_max_slack_beta
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a) :
    I.DualFeasible alpha (I.maxSlackBeta alpha) := by
  exact AdWordsInstance.dualFeasible_maxSlackBeta I alpha halpha

/--
The MSVV assignment-induced advertiser duals, paired with finite max-slack
query duals, form a dual-feasible AdWords LP solution.
-/
theorem paper_adwords_dual_feasible_msvv_assignment
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query) :
    I.DualFeasible (I.msvvAlphaFromAssignment A)
      (I.maxSlackBeta (I.msvvAlphaFromAssignment A)) := by
  exact AdWordsInstance.dualFeasible_msvvAssignment I A

/--
If some advertiser can still accept a query, a Balance/MSVV scaled-bid maximizer
exists for that query.
-/
theorem paper_adwords_balance_choice_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query) (q : Query)
    (h : ∃ a, I.CanAssign A q a) :
    ∃ a, I.IsBalanceChoice A q a := by
  exact AdWordsInstance.exists_balanceChoice_of_exists_canAssign I A q h

/--
Any feasible online choice rule preserves AdWords budget feasibility over a
finite query history.
-/
theorem paper_adwords_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.Feasible (I.runAssignment rule history) := by
  exact AdWordsInstance.runAssignment_feasible I hbudget rule hrule history

/--
The canonical Balance/MSVV scaled-bid choice rule preserves budget feasibility
over a finite query history.
-/
theorem paper_adwords_balance_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) :
    I.Feasible (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.balanceRunAssignment_feasible I hbudget history

/--
The Balance/MSVV run never assigns a query identifier that does not appear in
the input history.
-/
theorem paper_adwords_balance_assignment_assigned_only_from_history
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) {q : Query} {a : Advertiser}
    (hassigned : I.runAssignment I.balanceChoiceRule history q = some a) :
    q ∈ AdWordsInstance.historyFinset history := by
  exact AdWordsInstance.balanceRunAssignment_assigned_mem_historyFinset
    I hbudget history hassigned

/--
Spend is monotone along any feasible online AdWords run when bids are
nonnegative.
-/
theorem paper_adwords_spend_monotone_over_history
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) :
    I.spend S.assignment a ≤
      I.spend
        (I.runHistoryStateFrom rule S history).assignment a := by
  exact AdWordsInstance.spend_le_runHistoryStateFrom_spend
    I hbid rule hrule history S hS a

/--
MSVV monotonicity bridge: final assignment-induced slack scores are bounded by
the earlier Balance score at any prior state in the same run.
-/
theorem paper_adwords_final_slack_score_le_initial_balance_score
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) a q ≤
      I.balanceScore S.assignment a q := by
  exact AdWordsInstance.final_slackScore_le_initial_balanceScore
    I hbid rule hrule history S hS a q hbudget

/--
Non-exhausted-query beta charge: if every advertiser can still accept query
`q`, then the final max-slack query dual is bounded by the Balance score of the
advertiser selected at that state.
-/
theorem paper_adwords_max_slack_beta_le_balance_score_of_all_can_assign
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : AdWordsInstance.ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query)
    (S : AdWordsInstance.HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen)
    (hall : ∀ a, I.CanAssign S.assignment q a) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (I.runHistoryStateFrom rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q := by
  exact AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_balanceScore_of_all_canAssign
    I hbid hbudget rule hrule history S hS q chosen hchoice hall

/--
Small-bids boundary lemma: if advertiser `a` cannot accept query `q`, then
under the `ε`-small-bids condition `a` has already spent more than a
`1 - ε` fraction of her budget.
-/
theorem paper_adwords_small_bids_blocked_advertiser_spent_fraction
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : AdWordsInstance.Assignment Advertiser Query)
    (a : Advertiser) (q : Query) {ε : ℝ}
    (hbudget : 0 < I.budget a)
    (hsmall : I.SmallBids ε)
    (hnot : ¬ I.CanAssign A q a) :
    1 - ε < I.spentFraction A a := by
  exact AdWordsInstance.spentFraction_gt_one_sub_epsilon_of_not_canAssign
    I A a q hbudget hsmall hnot

/--
Paper-facing primal-dual seam: a finite primal-dual certificate implies the
advertised competitive-ratio inequality against the offline optimum.

For the full MSVV theorem, the remaining paper-specific work is to construct
this certificate for the Balance algorithm with ratio `1 - 1 / Real.exp 1`,
plus the paper's small-bids limiting argument.
-/
theorem paper_adwords_competitive_of_primal_dual_certificate
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : AdWordsInstance.Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.PrimalDualCompetitiveCertificate A ratio) :
    ratio * I.offlineOptimumValue hbudget ≤ I.revenue A := by
  exact AdWordsInstance.competitive_of_primalDual I hbudget A ratio hcert

/--
MSVV paper-facing seam for the Balance run: once the primal-dual certificate is
constructed for `msvvRatio = 1 - 1/e`, the Balance assignment is competitive
against the offline optimum at that ratio.
-/
theorem paper_adwords_balance_msvv_competitive_of_primal_dual_certificate
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query)
    (hcert :
      I.PrimalDualCompetitiveCertificate
        (I.runAssignment I.balanceChoiceRule history)
        AdWordsInstance.msvvRatio) :
    AdWordsInstance.msvvRatio * I.offlineOptimumValue hbudget ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.competitive_of_primalDual I hbudget
    (I.runAssignment I.balanceChoiceRule history)
    AdWordsInstance.msvvRatio hcert

/--
Final finite MSVV theorem seam: the Balance run is `1 - 1/e` competitive once
the single scaled dual-objective bound for the assignment-induced MSVV duals is
proved.
-/
theorem paper_adwords_balance_msvv_competitive_of_objective_bound
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query)
    (hcert : I.MsvvObjectiveBoundCertificate history) :
    AdWordsInstance.msvvRatio * I.offlineOptimumValue hbudget ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact AdWordsInstance.balance_msvv_competitive_of_objectiveBound
    I hbudget history hcert

end Online
end EconCSLean
