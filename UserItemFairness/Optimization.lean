import UserItemFairness.Basic

open scoped BigOperators
open DecisionCore

namespace UserItemFairness

/-- The set of recommendation-model values in which the estimated and true utilities differ. -/
structure EstimatedRecommendationModel (m n : ℕ) where
  trueModel : RecommendationModel m n
  estimatedUtility : User m → Item n → ℝ

namespace EstimatedRecommendationModel

/-- The recommendation model induced by the platform's estimated utility matrix. -/
def estimatedModel {m n : ℕ} (E : EstimatedRecommendationModel m n) : RecommendationModel m n where
  utility := E.estimatedUtility

end EstimatedRecommendationModel

namespace RecommendationModel

/-- Attainable minimum item-fairness values. -/
def attainableItemFairnessSet {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : Set ℝ :=
  {r | ∃ ρ : Policy m n, r = itemFairness W ρ}

/-- `I^*_min(w)` in the paper. -/
noncomputable def optimalItemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  sSup (attainableItemFairnessSet W)

/-- Feasibility for the paper's `γ`-constrained problem. -/
def feasibleAtLevel {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  γ * optimalItemFairness W ≤ itemFairness W ρ

/-- Attainable minimum user-fairness values subject to the item constraint. -/
def attainableUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set ℝ :=
  {r | ∃ ρ : Policy m n, feasibleAtLevel W γ ρ ∧ r = userFairness W ρ}

/-- Feasible user-fairness values are bounded above by one under positive row normalizers. -/
theorem attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) (γ : ℝ) :
    BddAbove (attainableUserFairnessAtLevel W γ) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, _hfeas, hr⟩ := hr
  rw [hr]
  exact userFairness_le_one_of_rowHasPositiveItem W hRow ρ

/-- A canonical policy used only to witness nonempty finite feasible sets. -/
noncomputable def defaultPolicy {m n : ℕ} [NeZero n] : Policy m n :=
  DecisionCore.Policy.pure
    (fun _ : User m => Classical.choice (inferInstance : Nonempty (Item n)))

/-- At baseline `γ = 0`, every policy is feasible under nonnegative utilities. -/
theorem feasibleAtLevel_zero_of_nonnegative {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) :
    feasibleAtLevel W 0 ρ := by
  unfold feasibleAtLevel
  simpa using itemFairness_nonneg_of_nonnegative W hNonneg ρ

/--
The baseline feasible value set is nonempty under nonnegative utilities. This
avoids a compactness argument for the paper's unconstrained item-fairness
baseline.
-/
theorem attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    (attainableUserFairnessAtLevel W 0).Nonempty := by
  refine ⟨userFairness W (defaultPolicy (m := m) (n := n)), ?_⟩
  exact ⟨defaultPolicy (m := m) (n := n),
    feasibleAtLevel_zero_of_nonnegative W hNonneg _, rfl⟩

/-- `U^*_min(γ, w)` in the paper. -/
noncomputable def optimalUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  sSup (attainableUserFairnessAtLevel W γ)

/-- A policy solves the paper's optimization problem at fairness level `γ`. -/
def IsOptimalAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  feasibleAtLevel W γ ρ ∧ userFairness W ρ = optimalUserFairnessAtLevel W γ

/-- The paper's price of fairness, generalized to an arbitrary `γ`. -/
noncomputable def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  let base := optimalUserFairnessAtLevel W 0
  if h : base = 0 then 0 else (base - optimalUserFairnessAtLevel W γ) / base

/-- The price of maximal item fairness on user fairness. -/
noncomputable def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/-- Problem 1 from the paper, as a predicate on candidate solution policies. -/
def SolvesProblemOne {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  IsOptimalAtLevel W γ ρ

end RecommendationModel

namespace EstimatedRecommendationModel

/-- A policy is optimal for the estimated utility matrix at level `γ`. -/
def SolvesEstimatedProblem {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  RecommendationModel.IsOptimalAtLevel E.estimatedModel γ ρ

/--
The paper's price of misestimation, evaluated on a chosen policy `ρ̂` that is intended
to solve the estimated problem.
-/
noncomputable def priceOfMisestimation {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n) : ℝ :=
  let base := RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ
  if h : base = 0 then 0 else
    (base - RecommendationModel.userFairness E.trueModel ρhat) / base

end EstimatedRecommendationModel
end UserItemFairness
