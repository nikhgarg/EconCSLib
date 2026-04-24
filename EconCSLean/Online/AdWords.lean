import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace EconCSLean
namespace Online

/--
Finite AdWords-style instance.

`budget a` is advertiser `a`'s budget and `bid a q` is the revenue/spend
contribution from assigning query `q` to advertiser `a`.
-/
structure AdWordsInstance (Advertiser Query : Type*) where
  budget : Advertiser → ℝ
  bid : Advertiser → Query → ℝ

namespace AdWordsInstance

variable {Advertiser Query : Type*}

/-- An offline assignment of every query to either one advertiser or nobody. -/
abbrev Assignment (Advertiser Query : Type*) :=
  Query → Option Advertiser

/-- Fractional AdWords assignment variables `x a q`. -/
abbrev FractionalAssignment (Advertiser Query : Type*) :=
  Advertiser → Query → ℝ

/-- The assignment that leaves every query unmatched. -/
def emptyAssignment : Assignment Advertiser Query :=
  fun _ => none

/-- Update an assignment by assigning query `q` to advertiser `a`. -/
def assignQuery [DecidableEq Query]
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    Assignment Advertiser Query :=
  fun q' => if q' = q then some a else A q'

/-- State carried by an online AdWords algorithm over a query history. -/
structure HistoryState (Advertiser Query : Type*) where
  assignment : Assignment Advertiser Query
  seen : Finset Query

/-- Initial online state: nothing assigned and no queries seen. -/
def initialHistoryState [DecidableEq Query] : HistoryState Advertiser Query where
  assignment := emptyAssignment
  seen := ∅

/-- The finite set of query identifiers appearing in a history list. -/
def historyFinset [DecidableEq Query] : List Query → Finset Query
  | [] => ∅
  | q :: qs => insert q (historyFinset qs)

/-- Spend charged to one advertiser by an assignment. -/
noncomputable def spend [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a' => if a' = a then I.bid a q else 0

/-- Total revenue of an assignment. -/
noncomputable def revenue [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a => I.bid a q

/-- Budget feasibility: no advertiser is charged above her budget. -/
def Feasible [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : Prop :=
  ∀ a, I.spend A a ≤ I.budget a

/-- Revenue of a fractional AdWords assignment. -/
noncomputable def fractionalRevenue
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query) : ℝ :=
  ∑ q : Query, ∑ a : Advertiser, I.bid a q * X a q

/--
Feasibility of the standard fractional AdWords LP: nonnegative assignment
variables, at most one unit assigned per query, and advertiser budget
constraints.
-/
structure FractionalFeasible
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query) : Prop where
  nonneg : ∀ a q, 0 ≤ X a q
  query : ∀ q, (∑ a : Advertiser, X a q) ≤ 1
  budget : ∀ a, (∑ q : Query, I.bid a q * X a q) ≤ I.budget a

/-- Embed an integral assignment as a `0/1` fractional assignment. -/
def assignmentFraction [DecidableEq Advertiser]
    (A : Assignment Advertiser Query) :
    FractionalAssignment Advertiser Query :=
  fun a q =>
    match A q with
    | none => 0
    | some owner => if owner = a then 1 else 0

/-- Remaining budget for advertiser `a` under assignment `A`. -/
noncomputable def residualBudget [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  I.budget a - I.spend A a

/--
An advertiser can accept query `q` after the partial assignment `A` if adding
the query's bid would still respect her budget.
-/
def CanAssign [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  I.spend A a + I.bid a q ≤ I.budget a

/-- Entrywise nonnegative bids. -/
def NonnegativeBids (I : AdWordsInstance Advertiser Query) : Prop :=
  ∀ a q, 0 ≤ I.bid a q

/-- Nonnegative advertiser budgets. -/
def NonnegativeBudgets (I : AdWordsInstance Advertiser Query) : Prop :=
  ∀ a, 0 ≤ I.budget a

/-- Strictly positive advertiser budgets. -/
def PositiveBudgets (I : AdWordsInstance Advertiser Query) : Prop :=
  ∀ a, 0 < I.budget a

/-- Small-bids condition: every bid is at most an `ε` fraction of the budget. -/
def SmallBids (I : AdWordsInstance Advertiser Query) (ε : ℝ) : Prop :=
  ∀ a q, I.bid a q ≤ ε * I.budget a

/-- A choice rule maps the current assignment and query to an optional advertiser. -/
abbrev ChoiceRule (Advertiser Query : Type*) :=
  Assignment Advertiser Query → Query → Option Advertiser

/--
A choice rule is feasible if every advertiser it returns can accept the query
under the current assignment.
-/
def ChoiceRuleFeasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) : Prop :=
  ∀ A q a, rule A q = some a → I.CanAssign A q a

/--
Online-state invariant: the current assignment is budget-feasible and every
query outside the `seen` set is still unassigned.
-/
def StateInvariant
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (S : HistoryState Advertiser Query) : Prop :=
  I.Feasible S.assignment ∧ ∀ q, q ∉ S.seen → S.assignment q = none

/--
The finite set of feasible offline assignments. This is the offline benchmark
domain for AdWords-style competitive-ratio statements.
-/
noncomputable def feasibleAssignments
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    Finset (Assignment Advertiser Query) := by
  classical
  exact Finset.univ.filter fun A => I.Feasible A

/-- An assignment is offline-optimal if it is feasible and dominates all feasible assignments. -/
def IsOptimalAssignment [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : Prop :=
  I.Feasible A ∧ ∀ B, I.Feasible B → I.revenue B ≤ I.revenue A

/--
Dual feasibility for the standard AdWords LP relaxation:
`bid a q ≤ bid a q * alpha a + beta q`, with nonnegative dual variables.
-/
structure DualFeasible
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ) : Prop where
  alpha_nonneg : ∀ a, 0 ≤ alpha a
  beta_nonneg : ∀ q, 0 ≤ beta q
  covers : ∀ a q, I.bid a q ≤ I.bid a q * alpha a + beta q

/-- Objective value of an AdWords LP dual solution. -/
noncomputable def dualObjective
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ) : ℝ :=
  (∑ a : Advertiser, I.budget a * alpha a) + ∑ q : Query, beta q

/--
The part of the dual objective induced by advertisers actually assigned by an
offline assignment.
-/
noncomputable def assignedWeightedSpend
    [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (alpha : Advertiser → ℝ) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a => I.bid a q * alpha a

/-- The fraction of advertiser `a`'s budget already spent. -/
noncomputable def spentFraction [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  I.spend A a / I.budget a

/--
The MSVV/Balance discount factor as a function of used budget fraction.
For fractions in `[0, 1]`, this lies in `[0, 1]`.
-/
noncomputable def balanceDiscount (x : ℝ) : ℝ :=
  1 - Real.exp (x - 1)

/-- The MSVV dual variable as a function of used budget fraction. -/
noncomputable def msvvDualAlpha (x : ℝ) : ℝ :=
  Real.exp (x - 1)

/-- The classical MSVV competitive ratio `1 - 1/e`. -/
noncomputable def msvvRatio : ℝ :=
  1 - 1 / Real.exp 1

/-- Balance/MSVV scaled bid for assigning query `q` to advertiser `a`. -/
noncomputable def balanceScore [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * balanceDiscount (I.spentFraction A a)

/-- Slack-score form of a dual covering constraint for one advertiser-query pair. -/
noncomputable def slackScore
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * (1 - alpha a)

/--
For a fixed advertiser dual `alpha`, choose the nonnegative query dual `beta q`
as the maximum advertiser slack score for query `q`, floored at zero.
-/
noncomputable def maxSlackBeta
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (q : Query) : ℝ := by
  classical
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  have hscores : scores.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty Advertiser)
    exact ⟨I.slackScore alpha a q, by simp [scores]⟩
  exact max 0 (scores.max' hscores)

/-- Feasible advertisers for the next query under the current partial assignment. -/
noncomputable def feasibleAdvertisers
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) :
    Finset Advertiser := by
  classical
  exact Finset.univ.filter fun a => I.CanAssign A q a

/--
A Balance/MSVV choice maximizes the scaled bid over advertisers that can still
accept the query without exceeding budget.
-/
def IsBalanceChoice
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  I.CanAssign A q a ∧
    ∀ b, I.CanAssign A q b → I.balanceScore A b q ≤ I.balanceScore A a q

/--
One online update step. Repeated queries are marked as seen but not reassigned;
new queries are assigned according to the choice rule when it returns an
advertiser.
-/
def stepHistoryState
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (_I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query) :
    HistoryState Advertiser Query :=
  if q ∈ S.seen then
    { S with seen := insert q S.seen }
  else
    match rule S.assignment q with
    | none => { assignment := S.assignment, seen := insert q S.seen }
    | some a =>
        { assignment := assignQuery S.assignment q a
          seen := insert q S.seen }

/-- Run an online choice rule from an arbitrary state over a finite query history. -/
def runHistoryStateFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) :
    HistoryState Advertiser Query → List Query → HistoryState Advertiser Query
  | S, [] => S
  | S, q :: qs => runHistoryStateFrom I rule (stepHistoryState I rule S q) qs

/-- Run an online choice rule from the initial empty state. -/
def runHistoryState
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) (history : List Query) :
    HistoryState Advertiser Query :=
  runHistoryStateFrom I rule initialHistoryState history

/-- The final assignment returned by an online choice rule on a query history. -/
def runAssignment
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) (history : List Query) :
    Assignment Advertiser Query :=
  (runHistoryState I rule history).assignment

/--
A reusable certificate for the competitive-ratio conclusion. The hard paper
proof supplies this certificate for the Balance/MSVV algorithm with ratio
`1 - 1 / Real.exp 1` in the small-bids limit.
-/
structure CompetitiveRatioCertificate
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (ratio : ℝ) : Prop where
  feasible : I.Feasible A
  competitive :
    ∀ Opt, I.IsOptimalAssignment Opt → ratio * I.revenue Opt ≤ I.revenue A

/--
A primal-dual certificate for a competitive ratio. The paper's charging
argument can be isolated to constructing `alpha`, `beta`, and the final scaled
dual-objective bound for the algorithm's assignment.
-/
structure PrimalDualCompetitiveCertificate
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (ratio : ℝ) where
  feasible : I.Feasible A
  ratio_nonneg : 0 ≤ ratio
  alpha : Advertiser → ℝ
  beta : Query → ℝ
  dual_feasible : I.DualFeasible alpha beta
  scaled_dual_bound : ratio * I.dualObjective alpha beta ≤ I.revenue A

theorem spend_emptyAssignment [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (a : Advertiser) :
    I.spend (emptyAssignment : Assignment Advertiser Query) a = 0 := by
  simp [spend, emptyAssignment]

theorem revenue_emptyAssignment [Fintype Query]
    (I : AdWordsInstance Advertiser Query) :
    I.revenue (emptyAssignment : Assignment Advertiser Query) = 0 := by
  simp [revenue, emptyAssignment]

theorem emptyAssignment_feasible [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.Feasible (emptyAssignment : Assignment Advertiser Query) := by
  intro a
  rw [spend_emptyAssignment]
  exact hbudget a

@[simp]
theorem assignQuery_apply_self [DecidableEq Query]
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    assignQuery A q a q = some a := by
  simp [assignQuery]

theorem assignQuery_apply_ne [DecidableEq Query]
    (A : Assignment Advertiser Query) {q q' : Query} (a : Advertiser)
    (hne : q' ≠ q) :
    assignQuery A q a q' = A q' := by
  simp [assignQuery, hne]

theorem spend_assignQuery_self_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hunassigned : A q = none) :
    I.spend (assignQuery A q a) a = I.spend A a + I.bid a q := by
  classical
  unfold spend assignQuery
  calc
    (∑ q' : Query,
        match (if q' = q then some a else A q') with
        | none => 0
        | some a' => if a' = a then I.bid a q' else 0) =
        ∑ q' : Query,
          ((match A q' with
            | none => 0
            | some a' => if a' = a then I.bid a q' else 0) +
            if q' = q then I.bid a q else 0) := by
      apply Finset.sum_congr rfl
      intro q' _hq'
      by_cases hq : q' = q
      · subst q'
        simp [hunassigned]
      · simp [hq]
    _ = (∑ q' : Query,
          match A q' with
          | none => 0
          | some a' => if a' = a then I.bid a q' else 0) +
        ∑ q' : Query, (if q' = q then I.bid a q else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ q' : Query,
          match A q' with
          | none => 0
          | some a' => if a' = a then I.bid a q' else 0) + I.bid a q := by
      rw [Finset.sum_ite_eq']
      simp

theorem spend_assignQuery_other_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) {a b : Advertiser}
    (hunassigned : A q = none) (hne : b ≠ a) :
    I.spend (assignQuery A q a) b = I.spend A b := by
  classical
  unfold spend assignQuery
  apply Finset.sum_congr rfl
  intro q' _hq'
  by_cases hq : q' = q
  · subst q'
    simp [hunassigned, hne.symm]
  · simp [hq]

theorem feasible_assignQuery_of_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hfeasible : I.Feasible A)
    (hunassigned : A q = none)
    (hcan : I.CanAssign A q a) :
    I.Feasible (assignQuery A q a) := by
  intro b
  by_cases hb : b = a
  · subst b
    rw [spend_assignQuery_self_of_unassigned I A q a hunassigned]
    exact hcan
  · rw [spend_assignQuery_other_of_unassigned I A q hunassigned hb]
    exact hfeasible b

theorem initialHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.StateInvariant (initialHistoryState : HistoryState Advertiser Query) := by
  constructor
  · exact emptyAssignment_feasible I hbudget
  · intro q _hq
    rfl

theorem residualBudget_nonneg_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser)
    (hfeasible : I.Feasible A) :
    0 ≤ I.residualBudget A a := by
  unfold residualBudget
  exact sub_nonneg.mpr (hfeasible a)

theorem canAssign_iff_bid_le_residualBudget
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    I.CanAssign A q a ↔ I.bid a q ≤ I.residualBudget A a := by
  unfold CanAssign residualBudget
  constructor <;> intro h <;> linarith

theorem spend_nonneg [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (a : Advertiser) :
    0 ≤ I.spend A a := by
  classical
  unfold spend
  exact Finset.sum_nonneg fun q _ => by
    cases hassign : A q with
    | none =>
        simp
    | some a' =>
        by_cases ha : a' = a
        · simpa [hassign, ha] using hbid a q
        · simp [ha]

theorem revenue_nonneg [Fintype Query]
    (I : AdWordsInstance Advertiser Query) (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) :
    0 ≤ I.revenue A := by
  classical
  unfold revenue
  exact Finset.sum_nonneg fun q _ => by
    cases hassign : A q with
    | none =>
        simp
    | some a =>
        simpa [hassign] using hbid a q

theorem revenue_eq_sum_spend
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    I.revenue A = ∑ a : Advertiser, I.spend A a := by
  classical
  unfold revenue spend
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  cases hassign : A q with
  | none =>
      simp
  | some owner =>
      simp

theorem revenue_le_totalBudget_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.revenue A ≤ ∑ a : Advertiser, I.budget a := by
  calc
    I.revenue A = ∑ a : Advertiser, I.spend A a :=
      revenue_eq_sum_spend I A
    _ ≤ ∑ a : Advertiser, I.budget a :=
      Finset.sum_le_sum fun a _ => hfeasible a

theorem assignmentFraction_nonneg
    [DecidableEq Advertiser]
    (A : Assignment Advertiser Query) :
    ∀ a q, 0 ≤ assignmentFraction A a q := by
  intro a q
  unfold assignmentFraction
  cases A q with
  | none =>
      simp
  | some owner =>
      by_cases h : owner = a <;> simp [h]

theorem assignmentFraction_query_sum_le_one
    [Fintype Advertiser] [DecidableEq Advertiser]
    (A : Assignment Advertiser Query) (q : Query) :
    (∑ a : Advertiser, assignmentFraction A a q) ≤ 1 := by
  classical
  unfold assignmentFraction
  cases A q with
  | none =>
      simp
  | some owner =>
      simp

theorem assignmentFraction_budget_sum_eq_spend
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) :
    (∑ q : Query, I.bid a q * assignmentFraction A a q) =
      I.spend A a := by
  classical
  unfold assignmentFraction spend
  apply Finset.sum_congr rfl
  intro q _hq
  cases hassign : A q with
  | none =>
      simp
  | some owner =>
      by_cases h : owner = a
      · subst owner
        simp
      · simp [h]

theorem assignmentFraction_fractionalFeasible_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.FractionalFeasible (assignmentFraction A) where
  nonneg := assignmentFraction_nonneg A
  query := assignmentFraction_query_sum_le_one A
  budget := by
    intro a
    rw [assignmentFraction_budget_sum_eq_spend I A a]
    exact hfeasible a

theorem fractionalRevenue_assignmentFraction_eq_revenue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    I.fractionalRevenue (assignmentFraction A) = I.revenue A := by
  classical
  unfold fractionalRevenue revenue assignmentFraction
  apply Finset.sum_congr rfl
  intro q _hq
  cases A q with
  | none =>
      simp
  | some owner =>
      simp

theorem fractional_dual_expansion
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ) :
    (∑ q : Query, ∑ a : Advertiser,
        (I.bid a q * alpha a + beta q) * X a q) =
      (∑ a : Advertiser, (∑ q : Query, I.bid a q * X a q) * alpha a) +
        ∑ q : Query, beta q * ∑ a : Advertiser, X a q := by
  classical
  calc
    (∑ q : Query, ∑ a : Advertiser,
        (I.bid a q * alpha a + beta q) * X a q) =
        ∑ q : Query, ∑ a : Advertiser,
          ((I.bid a q * X a q) * alpha a + beta q * X a q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ =
        (∑ q : Query, ∑ a : Advertiser,
          (I.bid a q * X a q) * alpha a) +
          ∑ q : Query, ∑ a : Advertiser, beta q * X a q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [← Finset.sum_add_distrib]
    _ =
        (∑ a : Advertiser, ∑ q : Query,
          (I.bid a q * X a q) * alpha a) +
          ∑ q : Query, ∑ a : Advertiser, beta q * X a q := by
      rw [Finset.sum_comm]
    _ =
        (∑ a : Advertiser, (∑ q : Query, I.bid a q * X a q) * alpha a) +
          ∑ q : Query, beta q * ∑ a : Advertiser, X a q := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]

theorem fractionalRevenue_le_dualObjective_of_dualFeasible
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible X)
    (hdual : I.DualFeasible alpha beta) :
    I.fractionalRevenue X ≤ I.dualObjective alpha beta := by
  have hpoint :
      I.fractionalRevenue X ≤
        ∑ q : Query, ∑ a : Advertiser,
          (I.bid a q * alpha a + beta q) * X a q := by
    unfold fractionalRevenue
    exact Finset.sum_le_sum fun q _ =>
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hdual.covers a q)
          (hfeasible.nonneg a q)
  have hbudget :
      (∑ a : Advertiser, (∑ q : Query, I.bid a q * X a q) * alpha a) ≤
        ∑ a : Advertiser, I.budget a * alpha a := by
    exact Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (hfeasible.budget a)
        (hdual.alpha_nonneg a)
  have hquery :
      (∑ q : Query, beta q * ∑ a : Advertiser, X a q) ≤
        ∑ q : Query, beta q := by
    exact Finset.sum_le_sum fun q _ => by
      have hmul :=
        mul_le_mul_of_nonneg_left (hfeasible.query q)
          (hdual.beta_nonneg q)
      simpa using hmul
  rw [fractional_dual_expansion I X alpha beta] at hpoint
  unfold dualObjective
  linarith

theorem assignedWeightedSpend_eq_sum_spend_mul
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (alpha : Advertiser → ℝ) :
    I.assignedWeightedSpend A alpha =
      ∑ a : Advertiser, I.spend A a * alpha a := by
  classical
  calc
    I.assignedWeightedSpend A alpha =
        ∑ q : Query, ∑ a : Advertiser,
          match A q with
          | none => 0
          | some owner => if owner = a then I.bid a q * alpha a else 0 := by
      unfold assignedWeightedSpend
      apply Finset.sum_congr rfl
      intro q _hq
      cases A q <;> simp
    _ = ∑ a : Advertiser, ∑ q : Query,
          match A q with
          | none => 0
          | some owner => if owner = a then I.bid a q * alpha a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a : Advertiser, I.spend A a * alpha a := by
      apply Finset.sum_congr rfl
      intro a _ha
      unfold spend
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _hq
      cases A q with
      | none =>
          simp
      | some owner =>
          by_cases h : owner = a <;> simp [h]

theorem assignedWeightedSpend_le_budget_weighted_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (alpha : Advertiser → ℝ)
    (hfeasible : I.Feasible A)
    (halpha : ∀ a, 0 ≤ alpha a) :
    I.assignedWeightedSpend A alpha ≤
      ∑ a : Advertiser, I.budget a * alpha a := by
  rw [assignedWeightedSpend_eq_sum_spend_mul]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_right (hfeasible a) (halpha a)

theorem revenue_le_assignedWeightedSpend_add_beta_of_dualFeasible
    [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hdual : I.DualFeasible alpha beta) :
    I.revenue A ≤ I.assignedWeightedSpend A alpha + ∑ q : Query, beta q := by
  classical
  unfold revenue assignedWeightedSpend
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q _ => by
    cases A q with
    | none =>
        simpa using hdual.beta_nonneg q
    | some a =>
        exact hdual.covers a q

theorem revenue_le_dualObjective_of_dualFeasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.Feasible A)
    (hdual : I.DualFeasible alpha beta) :
    I.revenue A ≤ I.dualObjective alpha beta := by
  have hrev :=
    revenue_le_assignedWeightedSpend_add_beta_of_dualFeasible
      I A alpha beta hdual
  have hspend :=
    assignedWeightedSpend_le_budget_weighted_of_feasible
      I A alpha hfeasible hdual.alpha_nonneg
  unfold dualObjective
  linarith

theorem mem_feasibleAssignments
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    A ∈ I.feasibleAssignments ↔ I.Feasible A := by
  classical
  simp [feasibleAssignments]

theorem feasibleAssignments_nonempty
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.feasibleAssignments.Nonempty := by
  classical
  refine ⟨emptyAssignment, ?_⟩
  exact (mem_feasibleAssignments I
    (emptyAssignment : Assignment Advertiser Query)).2
    (emptyAssignment_feasible I hbudget)

set_option linter.unusedFintypeInType false in
theorem exists_optimalAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    ∃ A : Assignment Advertiser Query, I.IsOptimalAssignment A := by
  classical
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_max_image I.feasibleAssignments (fun A => I.revenue A)
      (feasibleAssignments_nonempty I hbudget)
  refine ⟨A, ?_, ?_⟩
  · exact (mem_feasibleAssignments I A).1 hA
  · intro B hB
    exact hmax B ((mem_feasibleAssignments I B).2 hB)

/-- A chosen offline optimum assignment. -/
noncomputable def offlineOptimumAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) : Assignment Advertiser Query :=
  Classical.choose (exists_optimalAssignment I hbudget)

/-- The offline optimum value used as the benchmark in competitive analysis. -/
noncomputable def offlineOptimumValue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) : ℝ :=
  I.revenue (I.offlineOptimumAssignment hbudget)

theorem offlineOptimumAssignment_isOptimal
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.IsOptimalAssignment (I.offlineOptimumAssignment hbudget) := by
  exact Classical.choose_spec (exists_optimalAssignment I hbudget)

theorem revenue_le_offlineOptimumValue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.revenue A ≤ I.offlineOptimumValue hbudget := by
  exact (offlineOptimumAssignment_isOptimal I hbudget).2 A hfeasible

theorem offlineOptimumValue_le_totalBudget
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.offlineOptimumValue hbudget ≤ ∑ a : Advertiser, I.budget a := by
  exact revenue_le_totalBudget_of_feasible I
    (I.offlineOptimumAssignment hbudget)
    (offlineOptimumAssignment_isOptimal I hbudget).1

theorem offlineOptimumValue_le_dualObjective_of_dualFeasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hdual : I.DualFeasible alpha beta) :
    I.offlineOptimumValue hbudget ≤ I.dualObjective alpha beta := by
  exact revenue_le_dualObjective_of_dualFeasible I
    (I.offlineOptimumAssignment hbudget) alpha beta
    (offlineOptimumAssignment_isOptimal I hbudget).1 hdual

theorem spentFraction_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (a : Advertiser)
    (hbudget : 0 < I.budget a) :
    0 ≤ I.spentFraction A a := by
  unfold spentFraction
  exact div_nonneg (spend_nonneg I hbid A a) hbudget.le

theorem spentFraction_le_one_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser)
    (hbudget : 0 < I.budget a)
    (hfeasible : I.Feasible A) :
    I.spentFraction A a ≤ 1 := by
  unfold spentFraction
  calc
    I.spend A a / I.budget a ≤ I.budget a / I.budget a :=
      div_le_div_of_nonneg_right (hfeasible a) hbudget.le
    _ = 1 := by
      exact div_self hbudget.ne'

theorem spentFraction_gt_one_sub_epsilon_of_not_canAssign
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query)
    {ε : ℝ}
    (hbudget : 0 < I.budget a)
    (hsmall : I.SmallBids ε)
    (hnot : ¬ I.CanAssign A q a) :
    1 - ε < I.spentFraction A a := by
  unfold CanAssign at hnot
  have hlt : I.budget a < I.spend A a + I.bid a q :=
    lt_of_not_ge hnot
  have hbidle : I.bid a q ≤ ε * I.budget a := hsmall a q
  have hlt' : I.budget a < I.spend A a + ε * I.budget a :=
    lt_of_lt_of_le hlt (add_le_add_right hbidle (I.spend A a))
  have hmul : (1 - ε) * I.budget a < I.spend A a := by
    nlinarith
  have hdiv :=
    div_lt_div_of_pos_right hmul hbudget
  have hleft :
      ((1 - ε) * I.budget a) / I.budget a = 1 - ε := by
    exact mul_div_cancel_right₀ _ hbudget.ne'
  simpa [spentFraction, hleft] using hdiv

theorem balanceDiscount_nonneg_of_le_one {x : ℝ} (hx : x ≤ 1) :
    0 ≤ balanceDiscount x := by
  unfold balanceDiscount
  have hexp : Real.exp (x - 1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  linarith

theorem balanceDiscount_le_one (x : ℝ) :
    balanceDiscount x ≤ 1 := by
  unfold balanceDiscount
  have hexp : 0 ≤ Real.exp (x - 1) := Real.exp_nonneg (x - 1)
  linarith

theorem balanceDiscount_mem_unit_interval_of_le_one {x : ℝ} (hx : x ≤ 1) :
    0 ≤ balanceDiscount x ∧ balanceDiscount x ≤ 1 :=
  ⟨balanceDiscount_nonneg_of_le_one hx, balanceDiscount_le_one x⟩

theorem msvvDualAlpha_pos (x : ℝ) :
    0 < msvvDualAlpha x := by
  unfold msvvDualAlpha
  exact Real.exp_pos (x - 1)

theorem msvvDualAlpha_nonneg (x : ℝ) :
    0 ≤ msvvDualAlpha x :=
  (msvvDualAlpha_pos x).le

theorem balanceDiscount_eq_one_sub_msvvDualAlpha (x : ℝ) :
    balanceDiscount x = 1 - msvvDualAlpha x := by
  rfl

theorem msvvRatio_pos : 0 < msvvRatio := by
  unfold msvvRatio
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hfrac_lt : 1 / Real.exp 1 < 1 := by
    exact (div_lt_one hexp_pos).2
      (Real.one_lt_exp_iff.mpr zero_lt_one)
  linarith

theorem msvvRatio_nonneg : 0 ≤ msvvRatio :=
  le_of_lt msvvRatio_pos

theorem msvvRatio_lt_one : msvvRatio < 1 := by
  unfold msvvRatio
  have hfrac_pos : 0 < 1 / Real.exp 1 := by
    positivity
  linarith

theorem balanceScore_nonneg_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hfeasible : I.Feasible A) :
    0 ≤ I.balanceScore A a q := by
  unfold balanceScore
  exact mul_nonneg (hbid a q)
    (balanceDiscount_nonneg_of_le_one
      (spentFraction_le_one_of_feasible I A a hbudget hfeasible))

theorem balanceScore_eq_slackScore_msvvDualAlpha
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) :
    I.balanceScore A a q =
      I.slackScore (fun b => msvvDualAlpha (I.spentFraction A b)) a q := by
  simp [balanceScore, balanceDiscount, slackScore, msvvDualAlpha]

theorem dualFeasible_of_slackScore_le_beta
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a)
    (hbeta : ∀ q, 0 ≤ beta q)
    (hcover : ∀ a q, I.slackScore alpha a q ≤ beta q) :
    I.DualFeasible alpha beta := by
  refine ⟨halpha, hbeta, ?_⟩
  intro a q
  have h := hcover a q
  unfold slackScore at h
  nlinarith

theorem slackScore_le_maxSlackBeta
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    I.slackScore alpha a q ≤ I.maxSlackBeta alpha q := by
  classical
  unfold maxSlackBeta
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  have hmem : I.slackScore alpha a q ∈ scores := by
    simp [scores]
  have hle_max : I.slackScore alpha a q ≤
      scores.max' ⟨I.slackScore alpha a q, hmem⟩ :=
    scores.le_max' (I.slackScore alpha a q) hmem
  exact hle_max.trans (le_max_right 0 _)

theorem maxSlackBeta_nonneg
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (q : Query) :
    0 ≤ I.maxSlackBeta alpha q := by
  classical
  unfold maxSlackBeta
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  exact le_max_left 0 (scores.max' _)

theorem dualFeasible_maxSlackBeta
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a) :
    I.DualFeasible alpha (I.maxSlackBeta alpha) := by
  exact dualFeasible_of_slackScore_le_beta I alpha (I.maxSlackBeta alpha)
    halpha (maxSlackBeta_nonneg I alpha)
    (slackScore_le_maxSlackBeta I alpha)

theorem mem_feasibleAdvertisers
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    a ∈ I.feasibleAdvertisers A q ↔ I.CanAssign A q a := by
  classical
  simp [feasibleAdvertisers]

theorem exists_balanceChoice_of_exists_canAssign
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query)
    (h : ∃ a, I.CanAssign A q a) :
    ∃ a, I.IsBalanceChoice A q a := by
  classical
  have hnonempty : (I.feasibleAdvertisers A q).Nonempty := by
    rcases h with ⟨a, ha⟩
    exact ⟨a, (mem_feasibleAdvertisers I A q a).2 ha⟩
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (I.feasibleAdvertisers A q)
      (fun a => I.balanceScore A a q) hnonempty
  refine ⟨a, ?_, ?_⟩
  · exact (mem_feasibleAdvertisers I A q a).1 ha
  · intro b hb
    exact hmax b ((mem_feasibleAdvertisers I A q b).2 hb)

/-- Canonical Balance/MSVV choice rule: pick a scaled-bid maximizer if one exists. -/
noncomputable def balanceChoiceRule
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    ChoiceRule Advertiser Query := by
  classical
  exact fun A q =>
    if h : ∃ a, I.CanAssign A q a then
      some (Classical.choose (exists_balanceChoice_of_exists_canAssign I A q h))
    else
      none

theorem balanceChoiceRule_isBalanceChoice_of_eq_some
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : I.balanceChoiceRule A q = some a) :
    I.IsBalanceChoice A q a := by
  classical
  unfold balanceChoiceRule at hchoice
  by_cases h : ∃ a, I.CanAssign A q a
  · simp [h] at hchoice
    have hspec :=
      Classical.choose_spec (exists_balanceChoice_of_exists_canAssign I A q h)
    simpa [← hchoice] using hspec
  · simp [h] at hchoice

theorem balanceChoiceRule_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    I.ChoiceRuleFeasible I.balanceChoiceRule := by
  intro A q a hchoice
  exact (balanceChoiceRule_isBalanceChoice_of_eq_some I A q a hchoice).1

set_option linter.flexible false in
theorem stepHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (S : HistoryState Advertiser Query) (q : Query)
    (hS : I.StateInvariant S) :
    I.StateInvariant (stepHistoryState I rule S q) := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepHistoryState, hseen]
    constructor
    · exact hS.1
    · intro q' hq'
      exact hS.2 q' hq'
  · cases hchoice : rule S.assignment q with
    | none =>
        simp [stepHistoryState, hseen, hchoice]
        constructor
        · exact hS.1
        · intro q' hq'
          have hnotseen : q' ∉ S.seen := by
            intro hin
            exact hq' (by simp [hin])
          exact hS.2 q' hnotseen
    | some a =>
        simp [stepHistoryState, hseen, hchoice]
        constructor
        · exact feasible_assignQuery_of_canAssign I S.assignment q a
            hS.1 (hS.2 q hseen) (hrule S.assignment q a hchoice)
        · intro q' hq'
          have hne : q' ≠ q := by
            intro heq
            apply hq'
            simp [heq]
          have hnotseen : q' ∉ S.seen := by
            intro hin
            exact hq' (by simp [hin])
          change assignQuery S.assignment q a q' = none
          rw [assignQuery_apply_ne S.assignment a hne]
          exact hS.2 q' hnotseen

theorem runHistoryStateFrom_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) :
    I.StateInvariant (runHistoryStateFrom I rule S history) := by
  induction history generalizing S with
  | nil =>
      exact hS
  | cons q qs ih =>
      exact ih (stepHistoryState I rule S q)
        (stepHistoryState_invariant I rule hrule S q hS)

theorem stepHistoryState_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query) :
    (stepHistoryState I rule S q).seen = insert q S.seen := by
  classical
  unfold stepHistoryState
  by_cases hseen : q ∈ S.seen
  · simp [hseen]
  · simp [hseen]
    cases rule S.assignment q <;> simp

theorem runHistoryStateFrom_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (history : List Query) (S : HistoryState Advertiser Query) :
    (runHistoryStateFrom I rule S history).seen =
      historyFinset history ∪ S.seen := by
  induction history generalizing S with
  | nil =>
      simp [runHistoryStateFrom, historyFinset]
  | cons q qs ih =>
      rw [runHistoryStateFrom, ih]
      rw [stepHistoryState_seen]
      ext q'
      simp [historyFinset, or_comm]

theorem runHistoryState_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) (history : List Query) :
    (runHistoryState I rule history).seen = historyFinset history := by
  unfold runHistoryState
  rw [runHistoryStateFrom_seen]
  ext q
  simp [initialHistoryState]

theorem runHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.StateInvariant (runHistoryState I rule history) := by
  exact runHistoryStateFrom_invariant I rule hrule history
    initialHistoryState (initialHistoryState_invariant I hbudget)

theorem runAssignment_feasible
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.Feasible (I.runAssignment rule history) := by
  exact (runHistoryState_invariant I hbudget rule hrule history).1

theorem runAssignment_unseen_eq_none
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) {q : Query}
    (hnot : q ∉ historyFinset history) :
    I.runAssignment rule history q = none := by
  have hinv := runHistoryState_invariant I hbudget rule hrule history
  have hseen := runHistoryState_seen I rule history
  exact hinv.2 q (by simpa [hseen] using hnot)

theorem runAssignment_assigned_mem_historyFinset
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) {q : Query} {a : Advertiser}
    (hassigned : I.runAssignment rule history q = some a) :
    q ∈ historyFinset history := by
  by_contra hnot
  have hnone :=
    runAssignment_unseen_eq_none I hbudget rule hrule history hnot
  rw [hassigned] at hnone
  contradiction

theorem balanceRunAssignment_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) :
    I.Feasible (I.runAssignment I.balanceChoiceRule history) := by
  exact runAssignment_feasible I hbudget I.balanceChoiceRule
    (balanceChoiceRule_feasible I) history

theorem balanceRunAssignment_unseen_eq_none
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) {q : Query}
    (hnot : q ∉ historyFinset history) :
    I.runAssignment I.balanceChoiceRule history q = none := by
  exact runAssignment_unseen_eq_none I hbudget I.balanceChoiceRule
    (balanceChoiceRule_feasible I) history hnot

theorem balanceRunAssignment_assigned_mem_historyFinset
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) {q : Query} {a : Advertiser}
    (hassigned : I.runAssignment I.balanceChoiceRule history q = some a) :
    q ∈ historyFinset history := by
  exact runAssignment_assigned_mem_historyFinset I hbudget I.balanceChoiceRule
    (balanceChoiceRule_feasible I) history hassigned

theorem competitive_of_certificate
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.CompetitiveRatioCertificate A ratio) :
    ratio * I.offlineOptimumValue hbudget ≤ I.revenue A := by
  exact hcert.competitive (I.offlineOptimumAssignment hbudget)
    (offlineOptimumAssignment_isOptimal I hbudget)

theorem competitiveRatioCertificate_of_primalDual
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.PrimalDualCompetitiveCertificate A ratio) :
    I.CompetitiveRatioCertificate A ratio := by
  refine ⟨hcert.feasible, ?_⟩
  intro Opt hOpt
  have hopt_dual :
      I.revenue Opt ≤ I.dualObjective hcert.alpha hcert.beta :=
    revenue_le_dualObjective_of_dualFeasible I Opt hcert.alpha hcert.beta
      hOpt.1 hcert.dual_feasible
  have hscaled :
      ratio * I.revenue Opt ≤
        ratio * I.dualObjective hcert.alpha hcert.beta :=
    mul_le_mul_of_nonneg_left hopt_dual hcert.ratio_nonneg
  exact hscaled.trans hcert.scaled_dual_bound

theorem competitive_of_primalDual
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.PrimalDualCompetitiveCertificate A ratio) :
    ratio * I.offlineOptimumValue hbudget ≤ I.revenue A := by
  exact competitive_of_certificate I hbudget A ratio
    (competitiveRatioCertificate_of_primalDual I A ratio hcert)

end AdWordsInstance

end Online
end EconCSLean
