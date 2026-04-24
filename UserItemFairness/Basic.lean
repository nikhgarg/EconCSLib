import DecisionCore

open scoped BigOperators
open DecisionCore

namespace UserItemFairness

/-- Users are indexed by `Fin m`. -/
abbrev User (m : ℕ) := Fin m

/-- Items are indexed by `Fin n`. -/
abbrev Item (n : ℕ) := Fin n

/-- A recommendation policy maps each user to a PMF over items. -/
abbrev Policy (m n : ℕ) := DecisionCore.Policy (User m) (Item n)

/--
A finite recommendation model with shared user/item utility matrix `w`.
This matches the theoretical setup in the user-item fairness paper.
-/
structure RecommendationModel (m n : ℕ) where
  utility : User m → Item n → ℝ

namespace RecommendationModel

/-- Entrywise nonnegativity of the utility matrix. -/
def Nonnegative {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ u j, 0 ≤ W.utility u j

/-- Every user has at least one strictly positive item. -/
def RowHasPositiveItem {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ u, ∃ j, 0 < W.utility u j

/-- Every item has strictly positive total demand under the utility matrix. -/
def ColumnHasPositiveDemand {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ j, 0 < ∑ u, W.utility u j

/-- Raw user utility `∑_j w_ij ρ_ij`. -/
noncomputable def rawUserUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  DecisionCore.Policy.agentScore ρ W.utility u

/-- The best achievable item for user `u`, i.e. `max_j w_ij`. -/
noncomputable def bestItemUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) : ℝ :=
  finiteMax (W.utility u)

/-- Normalized user utility `U_i(ρ)`. -/
noncomputable def normalizedUserUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  rawUserUtility W ρ u / bestItemUtility W u

/-- Minimum normalized user utility `U_min(ρ)`. -/
noncomputable def userFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  finiteMin (normalizedUserUtility W ρ)

/-- Row positivity makes the user-normalization denominator strictly positive. -/
theorem bestItemUtility_pos_of_rowHasPositiveItem {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) (u : User m) :
    0 < bestItemUtility W u := by
  obtain ⟨j, hj⟩ := hRow u
  exact lt_of_lt_of_le hj (DecisionCore.le_finiteMax (W.utility u) j)

/-- Minimum user fairness is bounded above by every user's normalized utility. -/
theorem userFairness_le_normalizedUserUtility {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) :
    userFairness W ρ ≤ normalizedUserUtility W ρ u := by
  exact DecisionCore.finiteMin_le (normalizedUserUtility W ρ) u

/-- A user's raw expected utility is at most that user's best item utility. -/
theorem rawUserUtility_le_bestItemUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) :
    rawUserUtility W ρ u ≤ bestItemUtility W u := by
  unfold rawUserUtility bestItemUtility DecisionCore.Policy.agentScore
  exact DecisionCore.pmfExp_le_of_forall_le (ρ u) (W.utility u)
    (DecisionCore.finiteMax (W.utility u))
    (fun j => DecisionCore.le_finiteMax (W.utility u) j)

/-- Positive row normalizers make every normalized user utility at most one. -/
theorem normalizedUserUtility_le_one_of_rowHasPositiveItem {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem)
    (ρ : Policy m n) (u : User m) :
    normalizedUserUtility W ρ u ≤ 1 := by
  have hraw := rawUserUtility_le_bestItemUtility W ρ u
  have hbest_pos := bestItemUtility_pos_of_rowHasPositiveItem W hRow u
  unfold normalizedUserUtility
  rw [div_le_iff₀ hbest_pos]
  simpa using hraw

/-- Minimum user fairness is bounded above by one. -/
theorem userFairness_le_one_of_rowHasPositiveItem {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem)
    (ρ : Policy m n) :
    userFairness W ρ ≤ 1 := by
  classical
  let u0 : User m := Classical.choice inferInstance
  exact (userFairness_le_normalizedUserUtility W ρ u0).trans
    (normalizedUserUtility_le_one_of_rowHasPositiveItem W hRow ρ u0)

/-- Raw utility accumulated by item `j` under policy `ρ`. -/
noncomputable def rawItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j * (ρ u j).toReal

/-- Normalizer `∑_i w_ij` for item `j`. -/
noncomputable def itemNormalizer {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j

/-- Normalized item utility `I_j(ρ)`. If the denominator is `0`, we set the value to `0`. -/
noncomputable def normalizedItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  let denom := itemNormalizer W j
  if h : denom = 0 then 0 else rawItemUtility W ρ j / denom

/-- Minimum normalized item utility `I_min(ρ)`. -/
noncomputable def itemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  finiteMin (normalizedItemUtility W ρ)

/--
The paper's set `S_symm` is built from users sharing utility rows.
This predicate records that utilities are identical within each user type.
-/
structure UserTypeAssignment (m K : ℕ) where
  toType : User m → Fin K

/-- Utilities agree within user types. -/
def UtilitiesAgreeWithinTypes {m n K : ℕ}
    (W : RecommendationModel m n) (τ : UserTypeAssignment m K) : Prop :=
  ∀ u u', τ.toType u = τ.toType u' → W.utility u = W.utility u'

end RecommendationModel
end UserItemFairness
