import GCG24UserItemFairness.Basic

open scoped BigOperators
open EconCSLib

namespace GCG24UserItemFairness

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

/--
The standard LP epigraph form of item-fairness maximization: `λ` is no larger
than every normalized item utility under policy `ρ`.
-/
def itemFairnessLPFeasible {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ) : Prop :=
  ∀ j : Item n, ell ≤ normalizedItemUtility W ρ j

/-- Feasible objective values in the LP epigraph form of item-fairness maximization. -/
def itemFairnessLPValueSet {m n : ℕ}
    (W : RecommendationModel m n) : Set ℝ :=
  {ell | ∃ ρ : Policy m n, itemFairnessLPFeasible W ρ ell}

/-- The optimal value of the LP epigraph form of item-fairness maximization. -/
noncomputable def optimalItemFairnessLPValue {m n : ℕ}
    (W : RecommendationModel m n) : ℝ :=
  sSup (itemFairnessLPValueSet W)

/-- The LP epigraph constraints are equivalent to `λ ≤ I_min(ρ,w)`. -/
theorem itemFairnessLPFeasible_iff_le_itemFairness
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ) :
    itemFairnessLPFeasible W ρ ell ↔ ell ≤ itemFairness W ρ := by
  constructor
  · intro h
    unfold itemFairness EconCSLib.finiteMin
    apply Finset.le_inf'
    intro j _hj
    exact h j
  · intro h j
    exact h.trans (EconCSLib.finiteMin_le (normalizedItemUtility W ρ) j)

/-- Nonnegative utilities bound every attainable original item-fairness value above by one. -/
theorem attainableItemFairnessSet_bddAbove_of_nonnegative {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    BddAbove (attainableItemFairnessSet W) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, hr⟩ := hr
  rw [hr]
  exact itemFairness_le_one_of_nonnegative W hNonneg ρ

/-- The LP epigraph value set is nonempty, witnessed by any policy's own minimum item utility. -/
theorem itemFairnessLPValueSet_nonempty {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) :
    (itemFairnessLPValueSet W).Nonempty := by
  refine ⟨itemFairness W (uniformPolicy (m := m) (n := n)), ?_⟩
  exact ⟨uniformPolicy (m := m) (n := n),
    (itemFairnessLPFeasible_iff_le_itemFairness
      W (uniformPolicy (m := m) (n := n))
      (itemFairness W (uniformPolicy (m := m) (n := n)))).mpr le_rfl⟩

/-- Nonnegative utilities bound the LP epigraph objective values above by one. -/
theorem itemFairnessLPValueSet_bddAbove_of_nonnegative
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    BddAbove (itemFairnessLPValueSet W) := by
  refine ⟨1, ?_⟩
  intro ell hell
  obtain ⟨ρ, hρ⟩ := hell
  have hle_item :
      ell ≤ itemFairness W ρ :=
    (itemFairnessLPFeasible_iff_le_itemFairness W ρ ell).mp hρ
  exact hle_item.trans (itemFairness_le_one_of_nonnegative W hNonneg ρ)

/--
Appendix C, Lemma 2 in max-min LP epigraph form: maximizing `λ` subject to
`λ ≤ I_j(ρ,w)` for every item has the same value as `I^*_min(w)`.
-/
theorem optimalItemFairnessLPValue_eq_optimalItemFairness_of_nonnegative
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    optimalItemFairnessLPValue W = optimalItemFairness W := by
  have hLPNonempty := itemFairnessLPValueSet_nonempty W
  have hLPBdd := itemFairnessLPValueSet_bddAbove_of_nonnegative W hNonneg
  have hItemNonempty : (attainableItemFairnessSet W).Nonempty := by
    exact ⟨itemFairness W (uniformPolicy (m := m) (n := n)),
      ⟨uniformPolicy (m := m) (n := n), rfl⟩⟩
  have hItemBdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
  apply le_antisymm
  · unfold optimalItemFairnessLPValue
    refine csSup_le hLPNonempty ?_
    intro ell hell
    obtain ⟨ρ, hρ⟩ := hell
    have hle_item :
        ell ≤ itemFairness W ρ :=
      (itemFairnessLPFeasible_iff_le_itemFairness W ρ ell).mp hρ
    have hitem_mem :
        itemFairness W ρ ∈ attainableItemFairnessSet W := by
      exact ⟨ρ, rfl⟩
    exact hle_item.trans (le_csSup hItemBdd hitem_mem)
  · unfold optimalItemFairness
    refine csSup_le hItemNonempty ?_
    intro r hr
    obtain ⟨ρ, hr⟩ := hr
    rw [hr]
    have hlp_mem :
        itemFairness W ρ ∈ itemFairnessLPValueSet W := by
      exact ⟨ρ,
        (itemFairnessLPFeasible_iff_le_itemFairness
          W ρ (itemFairness W ρ)).mpr le_rfl⟩
    exact le_csSup hLPBdd hlp_mem

/--
Positive item demand and nonnegative utilities make the original optimal
item-fairness value strictly positive.
-/
theorem optimalItemFairness_pos_of_columnHasPositiveDemand
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hCol : W.ColumnHasPositiveDemand) :
    0 < optimalItemFairness W := by
  have hbdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
  have hmem :
      itemFairness W (uniformPolicy (m := m) (n := n)) ∈
        attainableItemFairnessSet W := by
    exact ⟨uniformPolicy (m := m) (n := n), rfl⟩
  exact lt_of_lt_of_le
    (itemFairness_uniformPolicy_pos_of_columnHasPositiveDemand W hCol)
    (le_csSup hbdd hmem)

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
  EconCSLib.Policy.pure
    (fun _ : User m => Classical.choice (inferInstance : Nonempty (Item n)))

/-- The deterministic policy that recommends each user an item attaining their finite row maximum. -/
noncomputable def bestItemPolicy {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : Policy m n :=
  EconCSLib.Policy.pure
    (fun u : User m =>
      Classical.choose (EconCSLib.exists_finiteMax_eq (W.utility u)))

theorem bestItemPolicy_utility_eq_bestItemUtility
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) :
    W.utility u
        (Classical.choose (EconCSLib.exists_finiteMax_eq (W.utility u))) =
      bestItemUtility W u := by
  exact (Classical.choose_spec
    (EconCSLib.exists_finiteMax_eq (W.utility u))).symm

/-- The best-item policy gives each user their row maximum in raw utility. -/
theorem rawUserUtility_bestItemPolicy_eq_bestItemUtility
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) :
    rawUserUtility W (bestItemPolicy W) u = bestItemUtility W u := by
  unfold rawUserUtility bestItemPolicy
  rw [EconCSLib.Policy.agentScore_pure]
  exact bestItemPolicy_utility_eq_bestItemUtility W u

/-- Under positive row normalizers, the best-item policy gives every user normalized utility `1`. -/
theorem normalizedUserUtility_bestItemPolicy_eq_one
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) (u : User m) :
    normalizedUserUtility W (bestItemPolicy W) u = 1 := by
  unfold normalizedUserUtility
  rw [rawUserUtility_bestItemPolicy_eq_bestItemUtility]
  exact div_self (ne_of_gt (bestItemUtility_pos_of_rowHasPositiveItem W hRow u))

/--
Without item-fairness constraints, the deterministic best-item policy gives
minimum normalized user utility `1`.
-/
theorem userFairness_bestItemPolicy_eq_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) :
    userFairness W (bestItemPolicy W) = 1 := by
  unfold userFairness
  exact EconCSLib.finiteMin_eq_of_forall
    (normalizedUserUtility W (bestItemPolicy W)) 1
    (normalizedUserUtility_bestItemPolicy_eq_one W hRow)

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

/--
For any strict fraction `γ < 1`, positive item demand makes the original
`γ`-constrained feasible-value set nonempty. This uses the defining
approximation property of `sSup`; exact attainment is only needed at `γ = 1`.
-/
theorem attainableUserFairnessAtLevel_nonempty_of_gamma_lt_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hCol : W.ColumnHasPositiveDemand)
    {γ : ℝ} (hγ : γ < 1) :
    (attainableUserFairnessAtLevel W γ).Nonempty := by
  have hopt_pos := optimalItemFairness_pos_of_columnHasPositiveDemand W hNonneg hCol
  have hlt :
      γ * optimalItemFairness W < optimalItemFairness W := by
    simpa using (mul_lt_mul_of_pos_right hγ hopt_pos)
  have hitem_nonempty : (attainableItemFairnessSet W).Nonempty := by
    exact ⟨itemFairness W (uniformPolicy (m := m) (n := n)),
      ⟨uniformPolicy (m := m) (n := n), rfl⟩⟩
  obtain ⟨r, hrmem, hrgt⟩ :=
    exists_lt_of_lt_csSup hitem_nonempty hlt
  obtain ⟨ρ, hr⟩ := hrmem
  refine ⟨userFairness W ρ, ?_⟩
  refine ⟨ρ, ?_, rfl⟩
  unfold feasibleAtLevel
  rw [← hr]
  exact le_of_lt hrgt

/-- `U^*_min(γ, w)` in the paper. -/
noncomputable def optimalUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  sSup (attainableUserFairnessAtLevel W γ)

/--
The paper's unconstrained user-fairness optimum:
`U^*_min(w) = 1` when utilities are nonnegative and every user has a positive
row normalizer.
-/
theorem optimalUserFairnessAtLevel_zero_eq_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    optimalUserFairnessAtLevel W 0 = 1 := by
  have hset_nonempty :
      (attainableUserFairnessAtLevel W 0).Nonempty :=
    attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative W hNonneg
  have hbdd :
      BddAbove (attainableUserFairnessAtLevel W 0) :=
    attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem W hRow 0
  have hbest_mem :
      userFairness W (bestItemPolicy W) ∈
        attainableUserFairnessAtLevel W 0 := by
    exact ⟨bestItemPolicy W, feasibleAtLevel_zero_of_nonnegative W hNonneg _, rfl⟩
  apply le_antisymm
  · unfold optimalUserFairnessAtLevel
    refine csSup_le hset_nonempty ?_
    intro r hr
    obtain ⟨ρ, _hfeas, hr⟩ := hr
    rw [hr]
    exact userFairness_le_one_of_rowHasPositiveItem W hRow ρ
  · rw [← userFairness_bestItemPolicy_eq_one W hRow]
    unfold optimalUserFairnessAtLevel
    exact le_csSup hbdd hbest_mem

/-- A policy solves the paper's optimization problem at fairness level `γ`. -/
def IsOptimalAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  feasibleAtLevel W γ ρ ∧ userFairness W ρ = optimalUserFairnessAtLevel W γ

/-- The paper's price of fairness, generalized to an arbitrary `γ`. -/
noncomputable def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  let base := optimalUserFairnessAtLevel W 0
  if h : base = 0 then 0 else (base - optimalUserFairnessAtLevel W γ) / base

/--
When the unconstrained optimum is `1`, the price of fairness is just
`1 - U^*_min(γ,w)`.
-/
theorem priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) (γ : ℝ) :
    priceOfFairnessAt W γ = 1 - optimalUserFairnessAtLevel W γ := by
  unfold priceOfFairnessAt
  rw [optimalUserFairnessAtLevel_zero_eq_one W hNonneg hRow]
  simp

/-- The price of maximal item fairness on user fairness. -/
noncomputable def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/--
Paper-facing specialization of the price-of-fairness simplification at maximal
item fairness.
-/
theorem priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    priceOfFairness W = 1 - optimalUserFairnessAtLevel W 1 := by
  exact priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel W hNonneg hRow 1

/--
If the maximal-item-fairness constrained optimum weakly increases between two
models, then the price of fairness weakly decreases.
-/
theorem priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      optimalUserFairnessAtLevel W 1 ≤ optimalUserFairnessAtLevel W' 1) :
    priceOfFairness W' ≤ priceOfFairness W := by
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W hNonneg hRow]
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W' hNonneg' hRow']
  linarith

/--
Strict version of the price-of-fairness monotonicity algebra.
-/
theorem priceOfFairness_lt_of_optimalUserFairnessAtLevel_one_lt
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      optimalUserFairnessAtLevel W 1 < optimalUserFairnessAtLevel W' 1) :
    priceOfFairness W' < priceOfFairness W := by
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W hNonneg hRow]
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W' hNonneg' hRow']
  linarith

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
If the estimated utility matrix is exactly the true matrix, then the estimated
recommendation model is the true recommendation model.
-/
theorem estimatedModel_eq_true_of_estimatedUtility_eq_true
    {m n : ℕ} (E : EstimatedRecommendationModel m n)
    (h : E.estimatedUtility = E.trueModel.utility) :
    E.estimatedModel = E.trueModel := by
  cases E with
  | mk trueModel estimatedUtility =>
    cases trueModel
    simpa [estimatedModel] using h

/--
The paper's price of misestimation, evaluated on a chosen policy `ρ̂` that is intended
to solve the estimated problem.
-/
noncomputable def priceOfMisestimation {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n) : ℝ :=
  let base := RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ
  if h : base = 0 then 0 else
    (base - RecommendationModel.userFairness E.trueModel ρhat) / base

/--
Exact-estimation benchmark for the paper's price of misestimation: if the
estimated model is the true model and `ρ̂` solves the estimated problem, then
there is no loss from misestimation.
-/
theorem priceOfMisestimation_eq_zero_of_estimatedModel_eq_true
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hmodel : E.estimatedModel = E.trueModel)
    (hopt : E.SolvesEstimatedProblem γ ρhat) :
    E.priceOfMisestimation γ ρhat = 0 := by
  unfold SolvesEstimatedProblem at hopt
  rw [hmodel] at hopt
  have huser :
      RecommendationModel.userFairness E.trueModel ρhat =
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ := hopt.2
  unfold priceOfMisestimation
  by_cases hbase :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ = 0
  · simp [hbase]
  · simp [hbase, huser]

/--
Exact-estimation benchmark stated directly in terms of utility matrices.
-/
theorem priceOfMisestimation_eq_zero_of_estimatedUtility_eq_true
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hutility : E.estimatedUtility = E.trueModel.utility)
    (hopt : E.SolvesEstimatedProblem γ ρhat) :
    E.priceOfMisestimation γ ρhat = 0 := by
  exact E.priceOfMisestimation_eq_zero_of_estimatedModel_eq_true γ ρhat
    (E.estimatedModel_eq_true_of_estimatedUtility_eq_true hutility) hopt

/--
When the true constrained optimum is positive, the price of misestimation is
`1 - U_min(ρhat,w) / U^*_min(γ,w)`.
-/
theorem priceOfMisestimation_eq_one_sub_userFairness_div
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hbase : 0 <
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ) :
    E.priceOfMisestimation γ ρhat =
      1 - RecommendationModel.userFairness E.trueModel ρhat /
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ := by
  unfold priceOfMisestimation
  simp [hbase.ne']
  field_simp [hbase.ne']

/--
If a candidate policy gives true user fairness less than an `eps` fraction of
the true optimum, its price of misestimation is greater than `1 - eps`.
-/
theorem priceOfMisestimation_gt_one_sub_of_userFairness_lt_mul_optimum
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ eps : ℝ) (ρhat : Policy m n)
    (hbase : 0 <
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ)
    (huser :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps * RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ) :
    1 - eps < E.priceOfMisestimation γ ρhat := by
  rw [E.priceOfMisestimation_eq_one_sub_userFairness_div γ ρhat hbase]
  have hratio :
      RecommendationModel.userFairness E.trueModel ρhat /
          RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ < eps := by
    rw [div_lt_iff₀ hbase]
    simpa [mul_comm] using huser
  linarith

/--
The final algebraic step in Appendix E's proof of Theorem 4: if the true
maximal-fairness optimum is above `1/n` while the estimated optimum's chosen
policy gives true user fairness below `eps/n`, then the price of
misestimation is above `1 - eps`.
-/
theorem priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (eps : ℝ) (ρhat : Policy m n)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (huser :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps / (n : ℝ)) :
    1 - eps < E.priceOfMisestimation 1 ρhat := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (NeZero.pos n)
  have hinv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
  have hbase_pos :
      0 < RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
    lt_trans hinv_pos hbase
  have huser_mul :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps * RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 := by
    have hscale :
        eps * (n : ℝ)⁻¹ <
          eps * RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
      mul_lt_mul_of_pos_left hbase heps
    exact lt_trans (by simpa [div_eq_mul_inv] using huser) hscale
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_mul_optimum
    1 eps ρhat hbase_pos huser_mul

/--
The first-bullet algebra in Theorem 4: if the unconstrained true optimum is
`1` and the policy chosen under estimated utilities gives true user fairness at
least `1/2`, then the price of misestimation without item-fairness constraints
is at most `1/2`.
-/
theorem priceOfMisestimation_at_zero_le_half_of_userFairness_ge_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (ρhat : Policy m n)
    (hbase :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 0 = 1)
    (huser :
      (1 / 2 : ℝ) ≤ RecommendationModel.userFairness E.trueModel ρhat) :
    E.priceOfMisestimation 0 ρhat ≤ (1 / 2 : ℝ) := by
  unfold priceOfMisestimation
  simp [hbase]
  linarith

end EstimatedRecommendationModel
end GCG24UserItemFairness
