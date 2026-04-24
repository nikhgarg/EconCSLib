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

/-- The assignment that leaves every query unmatched. -/
def emptyAssignment : Assignment Advertiser Query :=
  fun _ => none

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

/-- Balance/MSVV scaled bid for assigning query `q` to advertiser `a`. -/
noncomputable def balanceScore [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * balanceDiscount (I.spentFraction A a)

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
