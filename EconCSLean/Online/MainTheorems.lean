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

end Online
end EconCSLean
